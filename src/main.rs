#![deny(warnings, missing_debug_implementations, rust_2018_idioms)]

use std::{collections::HashSet, env, io::Write, result::Result as StdResult};

use anyhow::anyhow;
use chrono::{Datelike, NaiveDateTime};
use slog::{self, info, o, Drain};
use structopt::StructOpt;

const DEFAULT_TIMESTAMP_FORMAT: &str = "%Y-%m-%d-%H-%M-%S";

#[derive(Debug, StructOpt)]
/// Prunes `rdedup` names that do not match the given criteria. Names must be in a format matching
/// `<prefix><timestamp>` where timestamp is formatted as yyyy-mm-dd-HH-MM-SS. Alternate timestamp
/// formats may be specified with the --timestamp-format option.
/// Specifying a negative value for any --keep-* directive will result in an unlimited number for
/// that category. Specifying 0 disables the directive (the same as not specifying the directive at
/// all).
struct Opt {
    #[structopt(parse(from_occurrences), short = "v", long = "verbose")]
    /// Increase debugging level for general messages
    verbose: u32,
    #[structopt(parse(from_occurrences), short = "t", long = "verbose-timings")]
    /// Increase debugging level for timing messages
    verbose_timings: u32,
    #[structopt(
        short = "f",
        long = "timestamp-format",
        default_value = DEFAULT_TIMESTAMP_FORMAT
    )]
    /// Specify an alternate timestamp format string. Note that the timestamp format should be
    /// granular enough to satisfy the --keep-* directives specified.
    timestamp_format: String,
    #[structopt(short = "p", long = "prefix")]
    /// The prefix string for names to be pruned
    prefix: String,
    #[structopt(long = "no-prompt")]
    /// Do not prompt for confirmation prior to pruning entries
    no_prompt: bool,
    #[structopt(long = "skip-gc")]
    /// Do not perform a `gc` after names are removed
    skip_gc: bool,
    #[structopt(short = "n", long = "dry-run")]
    /// Dry-run only; do not prune any names
    dry_run: bool,
    #[structopt(long = "keep-within")]
    /// Keep names within the specified interval
    keep_within: Option<RetainWithin>,
    #[structopt(short = "H", long = "keep-hourly", default_value = "0")]
    /// Number of hourly archives to keep
    keep_hourly: i32,
    #[structopt(short = "d", long = "keep-daily", default_value = "0")]
    /// Number of daily archives to keep
    keep_daily: i32,
    #[structopt(short = "w", long = "keep-weekly", default_value = "0")]
    /// Number of weekly archives to keep
    keep_weekly: i32,
    #[structopt(short = "m", long = "keep-monthly", default_value = "0")]
    /// Number of monthly archives to keep
    keep_monthly: i32,
    #[structopt(short = "y", long = "keep-yearly", default_value = "0")]
    /// Number of yearly archives to keep
    keep_yearly: i32,
    #[structopt(long = "gc-grace", default_value = "86400")]
    /// Set grace time in seconds for `gc` command
    gc_grace_secs: u64,
}

type Error = anyhow::Error;
type Result<T> = StdResult<T, Error>;

fn create_logger(verbosity: u32, timing_verbosity: u32) -> slog::Logger {
    match (verbosity, timing_verbosity) {
        (0, 0) => slog::Logger::root(slog::Discard, o!()),
        (v, tv) => {
            let v = match v {
                0 => slog::Level::Warning,
                1 => slog::Level::Info,
                2 => slog::Level::Debug,
                _ => slog::Level::Trace,
            };
            let tv = match tv {
                0 => slog::Level::Warning,
                1 => slog::Level::Info,
                2 => slog::Level::Debug,
                _ => slog::Level::Trace,
            };
            let drain = slog_term::term_full();
            if verbosity > 4 {
                // at level 4, use synchronous logger so not to loose any
                // logging messages
                let drain = std::sync::Mutex::new(drain);
                let drain = slog::Filter::new(drain, move |record: &slog::Record<'_>| {
                    if record.tag() == "slog_perf" {
                        record.level() >= tv
                    } else {
                        record.level() >= v
                    }
                });
                let log = slog::Logger::root(drain.fuse(), o!());
                info!(
                    log,
                    "Using synchronized logging, that we'll be slightly slower."
                );
                log
            } else {
                let drain = slog_async::Async::default(drain.fuse());
                let drain = slog::Filter::new(drain, move |record: &slog::Record<'_>| {
                    if record.tag() == "slog_perf" {
                        record.level().is_at_least(tv)
                    } else {
                        record.level().is_at_least(v)
                    }
                });
                slog::Logger::root(drain.fuse(), o!())
            }
        }
    }
}

fn parse_timestamp(
    prefix_len: usize,
    timestamp_format: &str,
    name: String,
) -> (String, Option<NaiveDateTime>) {
    if prefix_len > name.len() {
        return (name, None);
    }

    let timestamp = NaiveDateTime::parse_from_str(&name[prefix_len..], timestamp_format).ok();
    (name, timestamp)
}

#[derive(Debug, PartialEq)]
enum RetainedBy {
    Within(RetainWithin),
    Hourly,
    Daily,
    Weekly,
    Monthly,
    Yearly,
}

#[derive(Debug, PartialEq)]
enum Action {
    Retain(RetainedBy),
    Remove,
    Ignore,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum TimeUnits {
    Hours,
    Days,
    Weeks,
    Months,
    Years,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct RetainWithin {
    count: u32,
    cutoff: NaiveDateTime,
    time_units: TimeUnits,
}

impl std::str::FromStr for RetainWithin {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let s = s.trim();
        if s.is_empty() {
            return Err(anyhow!("Empty --keep-within value specified"));
        }

        let count = s[0..s.len() - 1]
            .parse::<u32>()
            .map_err(|e| anyhow!("Failed to parse --keep-within value '{}': {}", s, e))?;

        if count == 0 {
            return Err(anyhow!("--keep-within value of 0 specified"));
        }

        if s.ends_with("H") || s.ends_with("h") {
            Ok(RetainWithin::hours(count))
        } else if s.ends_with("D") || s.ends_with("d") {
            Ok(RetainWithin::days(count))
        } else if s.ends_with("W") || s.ends_with("w") {
            Ok(RetainWithin::weeks(count))
        } else if s.ends_with("M") || s.ends_with("m") {
            Ok(RetainWithin::months(count))
        } else if s.ends_with("Y") || s.ends_with("y") {
            Ok(RetainWithin::years(count))
        } else {
            Err(anyhow!("Invalid --keep-within time unit '{}'; must be one of h(our), d(ay), w(eek), m(onth), or y(ear).", &s[s.len()-1..]))
        }
    }
}

impl RetainWithin {
    fn is_within(&self, timestamp: NaiveDateTime) -> bool {
        timestamp >= self.cutoff
    }

    fn hours(count: u32) -> RetainWithin {
        let cutoff =
            chrono::offset::Local::now().naive_local() - chrono::Duration::hours(count as i64);
        RetainWithin {
            count,
            cutoff,
            time_units: TimeUnits::Hours,
        }
    }

    fn days(count: u32) -> RetainWithin {
        let cutoff =
            chrono::offset::Local::now().naive_local() - chrono::Duration::days(count as i64);
        RetainWithin {
            count,
            cutoff,
            time_units: TimeUnits::Days,
        }
    }

    fn weeks(count: u32) -> RetainWithin {
        let cutoff =
            chrono::offset::Local::now().naive_local() - chrono::Duration::weeks(count as i64);
        RetainWithin {
            count,
            cutoff,
            time_units: TimeUnits::Weeks,
        }
    }

    fn months(count: u32) -> RetainWithin {
        let cutoff =
            chrono::offset::Local::now().naive_local() - chrono::Duration::days(count as i64 * 31);
        RetainWithin {
            count,
            cutoff,
            time_units: TimeUnits::Months,
        }
    }

    fn years(count: u32) -> RetainWithin {
        let cutoff =
            chrono::offset::Local::now().naive_local() - chrono::Duration::days(count as i64 * 365);
        RetainWithin {
            count,
            cutoff,
            time_units: TimeUnits::Years,
        }
    }
}

#[derive(Debug)]
enum RetentionCount {
    Count(u32),
    Unlimited,
}

impl RetentionCount {
    fn from_i32(count: i32) -> RetentionCount {
        if count < 0 {
            RetentionCount::Unlimited
        } else {
            RetentionCount::Count(count as u32)
        }
    }

    fn is_empty(&self) -> bool {
        match self {
            RetentionCount::Count(0) => true,
            _ => false,
        }
    }
}

struct RetentionRules {
    within: Option<RetainWithin>,
    hourly: RetentionCount,
    daily: RetentionCount,
    weekly: RetentionCount,
    monthly: RetentionCount,
    yearly: RetentionCount,
}

impl RetentionRules {
    fn from_opts(opts: &Opt) -> RetentionRules {
        let hourly = RetentionCount::from_i32(opts.keep_hourly);
        let daily = RetentionCount::from_i32(opts.keep_daily);
        let weekly = RetentionCount::from_i32(opts.keep_weekly);
        let monthly = RetentionCount::from_i32(opts.keep_monthly);
        let yearly = RetentionCount::from_i32(opts.keep_yearly);
        RetentionRules {
            within: None,
            hourly,
            daily,
            weekly,
            monthly,
            yearly,
        }
    }

    fn is_empty(&self) -> bool {
        self.within.is_none()
            && self.hourly.is_empty()
            && self.daily.is_empty()
            && self.weekly.is_empty()
            && self.monthly.is_empty()
            && self.yearly.is_empty()
    }

    fn is_within(&self, timestamp: NaiveDateTime) -> bool {
        self.within.map_or(false, |wi| wi.is_within(timestamp))
    }

    fn allow_more_hourly(&self, count: usize) -> bool {
        match self.hourly {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }

    fn allow_more_daily(&self, count: usize) -> bool {
        match self.daily {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }

    fn allow_more_weekly(&self, count: usize) -> bool {
        match self.weekly {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }

    fn allow_more_monthly(&self, count: usize) -> bool {
        match self.monthly {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }

    fn allow_more_yearly(&self, count: usize) -> bool {
        match self.yearly {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }
}

struct RetentionBins {
    retention_rules: RetentionRules,
    hourly_bins: HashSet<String>,
    daily_bins: HashSet<String>,
    weekly_bins: HashSet<String>,
    monthly_bins: HashSet<String>,
    yearly_bins: HashSet<i32>,
}

impl RetentionBins {
    fn new(retention_rules: RetentionRules) -> RetentionBins {
        RetentionBins {
            retention_rules,
            hourly_bins: HashSet::new(),
            daily_bins: HashSet::new(),
            weekly_bins: HashSet::new(),
            monthly_bins: HashSet::new(),
            yearly_bins: HashSet::new(),
        }
    }

    fn can_retain(&mut self, timestamp: NaiveDateTime) -> Action {
        if self.retention_rules.is_within(timestamp) {
            return Action::Retain(RetainedBy::Within(
                self.retention_rules
                    .within
                    .expect("Must be `Some` for `is_within` to return true"),
            ));
        }

        let hourly_key = timestamp.format("%Y%m%d%H").to_string();
        if self
            .retention_rules
            .allow_more_hourly(self.hourly_bins.len())
            && !self.hourly_bins.contains(&hourly_key)
        {
            self.hourly_bins.insert(hourly_key);
            return Action::Retain(RetainedBy::Hourly);
        }

        let daily_key = timestamp.format("%Y%m%d").to_string();
        if self.retention_rules.allow_more_daily(self.daily_bins.len())
            && !self.daily_bins.contains(&daily_key)
        {
            self.daily_bins.insert(daily_key);
            return Action::Retain(RetainedBy::Daily);
        }

        let weekly_key = timestamp.format("%Y%W").to_string();
        if self
            .retention_rules
            .allow_more_weekly(self.weekly_bins.len())
            && !self.weekly_bins.contains(&weekly_key)
        {
            self.weekly_bins.insert(weekly_key);
            return Action::Retain(RetainedBy::Weekly);
        }

        let monthly_key = timestamp.format("%Y%m").to_string();
        if self
            .retention_rules
            .allow_more_monthly(self.monthly_bins.len())
            && !self.monthly_bins.contains(&monthly_key)
        {
            self.monthly_bins.insert(monthly_key);
            return Action::Retain(RetainedBy::Monthly);
        }

        let yearly_key = timestamp.year();
        if self
            .retention_rules
            .allow_more_yearly(self.yearly_bins.len())
            && !self.yearly_bins.contains(&yearly_key)
        {
            self.yearly_bins.insert(yearly_key);
            return Action::Retain(RetainedBy::Yearly);
        }

        Action::Remove
    }
}

fn prune(keep: RetentionRules, names: &[(String, Option<NaiveDateTime>)]) -> Vec<(&str, Action)> {
    // partition based on whether it has a timestamp
    let (ignored, mut to_process): (Vec<_>, Vec<_>) =
        names.iter().partition(|(_, ts)| ts.is_none());

    let mut actions = Vec::with_capacity(names.len());
    for (name, _) in ignored {
        actions.push((name.as_str(), Action::Ignore));
    }

    let mut bins = RetentionBins::new(keep);

    to_process.sort();
    for (name, timestamp) in to_process.iter().rev() {
        // for each of hourly, daily, weekly, monthly, yearly
        // 1. check to see if it is last in its bucket, do not mark to retain
        // 2. if so, check if we are to retain more in that category
        let timestamp = timestamp.unwrap();
        actions.push((name.as_str(), bins.can_retain(timestamp)));
    }
    actions
}

fn main() -> Result<()> {
    let opts = Opt::from_args();

    let keep = RetentionRules::from_opts(&opts);
    if keep.is_empty() {
        return Err(anyhow!("No retention rules specified. At least one of --keep-{hourly,daily,weekly,monthly,yearly} must be specified with non-0 count, or all names would be pruned."));
    }

    let log = create_logger(opts.verbose, opts.verbose_timings);

    let url = if let Some(uri) = env::var_os("RDEDUP_URI") {
        if env::var_os("RDEDUP_DIR").is_some() {
            return Err(anyhow!(
                "Cannot specify both RDEDUP_DIR and RDEDUP_URI at the same time."
            ));
        }
        let uri = uri
            .into_string()
            .map_err(|uri| anyhow!("RDEDUP_DIR='{}' is not valid UTF-8", uri.to_string_lossy()))?;
        url::Url::parse(&uri)?
    } else if let Some(dir) = env::var_os("RDEDUP_DIR") {
        url::Url::from_file_path(&dir)
            .map_err(|_| anyhow!("URI parsing error: {}", dir.to_string_lossy()))?
    } else {
        return Err(anyhow!("Repository location not specified"));
    };

    let repo = rdedup_lib::Repo::open(&url, log)?;

    let prefix_len = opts.prefix.len();
    let names = repo
        .list_names()?
        .into_iter()
        .filter(|n| n.starts_with(&opts.prefix))
        .map(|n| parse_timestamp(prefix_len, &opts.timestamp_format, n))
        .collect::<Vec<_>>();

    let actions = prune(keep, &names[..]);

    for (name, action) in &actions {
        println!("{}: {:?}", name, action);
    }

    let to_remove = actions
        .into_iter()
        .filter(|(_, a)| a == &Action::Remove)
        .collect::<Vec<_>>();

    if to_remove.is_empty() {
        println!("No names need pruning.");
        return Ok(());
    }

    if opts.dry_run {
        println!("--dry-run specified, no action taken.");
        return Ok(());
    }

    if !opts.no_prompt {
        print!("Remove names [yN]? ");
        std::io::stdout().flush()?;
        let mut input = String::new();
        std::io::stdin().read_line(&mut input)?;
        if !input.to_lowercase().starts_with("y") {
            println!("Aborting.");
            return Ok(());
        }
    }

    for (name, _) in to_remove {
        print!("Removing {}...", name);
        std::io::stdout().flush()?;
        repo.rm(&name)?;
        println!("done");
    }

    if !opts.skip_gc {
        print!("Running GC...");
        std::io::stdout().flush()?;
        repo.gc(opts.gc_grace_secs)?;
        println!("done");
    } else {
        println!("--skip-gc specified, skipping GC.");
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn default_timestamps() {
        let name = "foo-2020-06-27-11-12-13".to_string();
        let timestamp = chrono::NaiveDate::from_ymd(2020, 6, 27).and_hms(11, 12, 13);
        let parsed = parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, name.clone());
        assert_eq!((name, Some(timestamp)), parsed)
    }

    #[test]
    fn alternate_timestamps() {
        let name = "foo-2020-06-27-11-12".to_string();
        let timestamp = chrono::NaiveDate::from_ymd(2020, 6, 27).and_hms(11, 12, 0);
        let parsed = parse_timestamp("foo-".len(), "%Y-%m-%d-%H-%M", name.clone());
        assert_eq!((name, Some(timestamp)), parsed)
    }

    #[test]
    fn bad_timestamps() {
        let names = vec![
            "".to_string(),
            "foo-".to_string(),
            "foo-not-a-timestamp".to_string(),
            "foo-2020-a6-27-11-12-13".to_string(),
            "foo-2020-06-27-11-12-93".to_string(),
        ];
        for name in names {
            let parsed = parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, name.clone());
            assert_eq!((name, None), parsed)
        }
    }

    #[test]
    fn no_retention() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-34-56".to_string(), Action::Remove),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_one_hourly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(1),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_multiple_hourly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            (
                "foo-2020-06-27-11-12-13".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(2),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_unlimited_hourly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            (
                "foo-2020-06-27-11-12-13".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            (
                "foo-2020-06-26-11-12-13".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            (
                "foo-2020-06-26-12-34-56".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Unlimited,
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_one_daily() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(1),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_multiple_daily() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            (
                "foo-2020-06-26-12-34-56".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
            ("foo-2020-06-25-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(2),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_unlimited_daily() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            (
                "foo-2020-06-26-12-34-56".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
            (
                "foo-2020-06-25-11-12-13".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Unlimited,
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_one_weekly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            ("foo-2020-06-25-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(1),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_multiple_weekly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            ("foo-2020-06-25-11-12-13".to_string(), Action::Remove),
            (
                "foo-2020-06-19-11-12-13".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
            ("foo-2020-06-11-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(2),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_unlimited_weekly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            ("foo-2020-06-25-11-12-13".to_string(), Action::Remove),
            (
                "foo-2020-06-19-11-12-13".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
            (
                "foo-2020-06-11-11-12-13".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Unlimited,
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_one_monthly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            ("foo-2020-06-25-11-12-13".to_string(), Action::Remove),
            ("foo-2020-05-19-11-12-13".to_string(), Action::Remove),
            ("foo-2020-04-11-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(1),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_multiple_monthly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            ("foo-2020-06-25-11-12-13".to_string(), Action::Remove),
            (
                "foo-2020-05-19-11-12-13".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
            ("foo-2020-04-11-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(2),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_unlimited_monthly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            ("foo-2020-06-25-11-12-13".to_string(), Action::Remove),
            (
                "foo-2020-05-19-11-12-13".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
            (
                "foo-2020-04-11-11-12-13".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Unlimited,
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_one_yearly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            ("foo-2019-06-25-11-12-13".to_string(), Action::Remove),
            ("foo-2019-05-19-11-12-13".to_string(), Action::Remove),
            ("foo-2018-04-11-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(1),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_multiple_yearly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            (
                "foo-2019-06-25-11-12-13".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
            ("foo-2019-05-19-11-12-13".to_string(), Action::Remove),
            ("foo-2018-04-11-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(2),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_unlimited_yearly() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            ("foo-2020-06-27-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-27-12-00-00".to_string(), Action::Remove),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
            ("foo-2020-06-26-11-12-13".to_string(), Action::Remove),
            ("foo-2020-06-26-12-34-56".to_string(), Action::Remove),
            (
                "foo-2019-06-25-11-12-13".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
            ("foo-2019-05-19-11-12-13".to_string(), Action::Remove),
            (
                "foo-2018-04-11-11-12-13".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Unlimited,
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_one_each() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            (
                "foo-2020-06-27-11-12-13".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
            (
                "foo-2020-06-27-12-00-00".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            (
                "foo-2020-06-26-11-12-13".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
            (
                "foo-2020-06-26-12-34-56".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
            ("foo-2019-06-25-11-12-13".to_string(), Action::Remove),
            ("foo-2019-05-19-11-12-13".to_string(), Action::Remove),
            ("foo-2018-04-11-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(1),
            daily: RetentionCount::Count(1),
            weekly: RetentionCount::Count(1),
            monthly: RetentionCount::Count(1),
            yearly: RetentionCount::Count(1),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }

    #[test]
    fn retain_multiple_each() {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            (
                "foo-2020-06-27-12-34-56".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            (
                "foo-2020-06-27-12-00-00".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
            (
                "foo-2020-06-27-11-12-13".to_string(),
                Action::Retain(RetainedBy::Hourly),
            ),
            (
                "foo-2020-06-27-10-01-23".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
            (
                "foo-2020-06-26-12-34-56".to_string(),
                Action::Retain(RetainedBy::Daily),
            ),
            (
                "foo-2020-06-26-11-12-13".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
            (
                "foo-2020-06-21-11-12-13".to_string(),
                Action::Retain(RetainedBy::Weekly),
            ),
            (
                "foo-2019-06-25-11-12-13".to_string(),
                Action::Retain(RetainedBy::Monthly),
            ),
            (
                "foo-2019-05-19-11-12-13".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
            ("foo-2019-04-11-11-12-13".to_string(), Action::Remove),
            (
                "foo-2016-04-11-11-12-13".to_string(),
                Action::Retain(RetainedBy::Yearly),
            ),
            ("foo-2015-04-11-11-12-13".to_string(), Action::Remove),
        ]
        .into_iter()
        .collect::<HashMap<_, _>>();

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(2),
            daily: RetentionCount::Count(2),
            weekly: RetentionCount::Count(2),
            monthly: RetentionCount::Count(2),
            yearly: RetentionCount::Count(2),
        };
        assert!(!keep.is_empty());

        let parsed = expected
            .keys()
            .map(|n| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        for (n, expected) in expected {
            assert_eq!(actions[n.as_str()], expected, "{}", n);
        }
    }
}
