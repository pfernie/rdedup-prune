#![deny(warnings, missing_debug_implementations, rust_2018_idioms)]
//! Prunes `rdedup` names that do not match the given criteria. Names must be in a format matching
//! `<prefix><timestamp>` where timestamp is formatted as yyyy-mm-dd-HH-MM-SS. Alternate timestamp
//! formats may be specified with the `--timestamp-format` option.
//!
//! Specifying a negative value for any of `--keep-{hourly,daily,weekly,monthly,yearly}` will result
//! in an unlimited number for that category. Specifying 0 disables the directive (the same as not
//! specifying the directive at all).
//!
//! The `--keep-within` rule specifies an interval in which to keep all names, which do not count
//! towards any counts for the `--keep-{hourly,daily,weekly,monthly,yearly}` rules. Intervals are
//! specified as <count><unit>, where count must be a positive integer, and unit if one of:
//!   * h - hours
//!   * d - days
//!   * w - weeks
//!   * m - months (31 days)
//!   * y - years (365 days)
//!
//! For example `--keep-within 1d -h 2 -d 2` would keep all names within a day, the most recent
//! 2 hourly names prior to a day ago, and the most recent daily names prior to a day ago.

use std::{collections::HashSet, env, io::Write, result::Result as StdResult};

use anyhow::anyhow;
use chrono::{Datelike, NaiveDateTime};
use slog::{self, info, o, Drain};
use structopt::StructOpt;

const DEFAULT_TIMESTAMP_FORMAT: &str = "%Y-%m-%d-%H-%M-%S";

#[derive(Debug, StructOpt)]
/// Prunes `rdedup` names that do not match the given criteria. Names must be in a format matching
/// `<prefix><timestamp>` where timestamp is formatted as yyyy-mm-dd-HH-MM-SS. Alternate timestamp
/// formats may be specified with the `--timestamp-format` option.
///
/// Specifying a negative value for any of `--keep-{hourly,daily,weekly,monthly,yearly}` will result
/// in an unlimited number for that category. Specifying 0 disables the directive (the same as not
/// specifying the directive at all).
///
/// The `--keep-within` rule specifies an interval in which to keep all names, which do not count
/// towards any counts for the `--keep-{hourly,daily,weekly,monthly,yearly}` rules. Intervals are
/// specified as <count><unit>, where count must be a positive integer, and unit if one of:
///   * h - hours
///   * d - days
///   * w - weeks
///   * m - months (31 days)
///   * y - years (365 days)
///
/// For example `--keep-within 1d -h 2 -d 2` would keep all names within a day, the most recent
/// 2 hourly names prior to a day ago, and the most recent daily names prior to a day ago.
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
    /// granular enough to satisfy the `--keep-*` directives specified.
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
    /// Keep names within the specified interval. Intervals may be specified as <count><unit>,
    /// where <unit> is one of: h(ours), d(ays), w(eeks), m(onths, 31 days), y(ears, 365 days)
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

/// Build an slog::Logger to pass into `rdedup`
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
/// Description of the rule used when a name is retained
enum RetainedBy {
    Within(RetainWithin),
    Hourly,
    Daily,
    Weekly,
    Monthly,
    Yearly,
}

#[derive(Debug, PartialEq)]
/// Prune action determined for a name
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

impl TimeUnits {
    /// Convenience method to convert our `TimeUnits` to a specific `Duration` given a `count`.
    fn duration(&self, count: i64) -> chrono::Duration {
        match self {
            TimeUnits::Hours => chrono::Duration::hours(count),
            TimeUnits::Days => chrono::Duration::days(count),
            TimeUnits::Weeks => chrono::Duration::weeks(count),
            TimeUnits::Months => chrono::Duration::days(count * 31),
            TimeUnits::Years => chrono::Duration::days(count * 365),
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
/// A rule indicating a cutoff time after which all names should be retained.
struct RetainWithin {
    /// `count` of `TimeUnits` the interval is for
    count: u32,
    /// The `TimeUnits` of the interval
    time_units: TimeUnits,
    /// The result of applying the interval to the current time
    cutoff: NaiveDateTime,
}

impl std::fmt::Debug for RetainWithin {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(
            fmt,
            "{} ({} {:?} ago)",
            self.cutoff.format(DEFAULT_TIMESTAMP_FORMAT),
            self.count,
            self.time_units
        )
    }
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
    /// Determine if a given `timestamp` is within the retention interval
    fn is_within(&self, timestamp: NaiveDateTime) -> bool {
        timestamp >= self.cutoff
    }

    /// Construct a new `RetainWithin` for the interval specified by `count` and `time_units`.
    fn new(time_units: TimeUnits, count: u32) -> RetainWithin {
        let cutoff = chrono::offset::Local::now().naive_local() - time_units.duration(count as i64);
        RetainWithin {
            count,
            cutoff,
            time_units,
        }
    }

    /// Construct a new `RetainWithin` for the specified number of hours
    fn hours(count: u32) -> RetainWithin {
        RetainWithin::new(TimeUnits::Hours, count)
    }

    /// Construct a new `RetainWithin` for the specified number of days
    fn days(count: u32) -> RetainWithin {
        RetainWithin::new(TimeUnits::Days, count)
    }

    /// Construct a new `RetainWithin` for the specified number of weeks
    fn weeks(count: u32) -> RetainWithin {
        RetainWithin::new(TimeUnits::Weeks, count)
    }

    /// Construct a new `RetainWithin` for the specified number of months
    fn months(count: u32) -> RetainWithin {
        RetainWithin::new(TimeUnits::Months, count)
    }

    /// Construct a new `RetainWithin` for the specified number of years
    fn years(count: u32) -> RetainWithin {
        RetainWithin::new(TimeUnits::Years, count)
    }
}

#[derive(Debug)]
/// Rules specifying a maximum number (`Count`) of names to retain for a bin, or an `Unlimited`
/// number.
enum RetentionCount {
    Count(u32),
    Unlimited,
}

impl RetentionCount {
    /// Create a `RetentionCount` from `count`. A negative `count` results in an `Unlimited`
    /// policy, otherwise `count` specifies the maximum number allowed. `0` therefore specifies a
    /// disabled criteria.
    fn from_i32(count: i32) -> RetentionCount {
        if count < 0 {
            RetentionCount::Unlimited
        } else {
            RetentionCount::Count(count as u32)
        }
    }

    /// If `Count` variant of `0`, then no names will be retained for these bins.
    fn is_empty(&self) -> bool {
        match self {
            RetentionCount::Count(0) => true,
            _ => false,
        }
    }
}

/// The set of retention rules to run against the set of names when evaluating candidates for
/// pruning.
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
            within: opts.keep_within,
            hourly,
            daily,
            weekly,
            monthly,
            yearly,
        }
    }

    /// If all the rules in this set disallow any retention, the set is considered empty.
    fn is_empty(&self) -> bool {
        self.within.is_none()
            && self.hourly.is_empty()
            && self.daily.is_empty()
            && self.weekly.is_empty()
            && self.monthly.is_empty()
            && self.yearly.is_empty()
    }

    /// If a `RetainWithin` rule is set, determine if `timestamp` is within that interval.
    fn is_within(&self, timestamp: NaiveDateTime) -> bool {
        self.within.map_or(false, |wi| wi.is_within(timestamp))
    }

    /// Determine if more `Hourly` bin names can be added
    fn allow_more_hourly(&self, count: usize) -> bool {
        match self.hourly {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }

    /// Determine if more `Daily` bin names can be added
    fn allow_more_daily(&self, count: usize) -> bool {
        match self.daily {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }

    /// Determine if more `Weekly` bin names can be added
    fn allow_more_weekly(&self, count: usize) -> bool {
        match self.weekly {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }

    /// Determine if more `Monthly` bin names can be added
    fn allow_more_monthly(&self, count: usize) -> bool {
        match self.monthly {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }

    /// Determine if more `Yearly` bin names can be added
    fn allow_more_yearly(&self, count: usize) -> bool {
        match self.yearly {
            RetentionCount::Count(c) => c as usize > count,
            RetentionCount::Unlimited => true,
        }
    }
}

/// The current sets of names that have been retained under a set of `RetentionRules`.
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

    /// Determine if `timestamp` can be retained via the current `RetentionRules`, either within
    /// the `RetainWithin` interval or in one of the `Hourly`, `Daily`, `Weekly`, `Monthly`, or
    /// `Yearly` bins.
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

/// Given a set of `RetentionRules`, `keep`, and set of `rdedup` names, determine what actions
/// should be taken
fn prune(keep: RetentionRules, names: &[(String, Option<NaiveDateTime>)]) -> Vec<(&str, Action)> {
    // partition based on whether it has a timestamp
    let (ignored, mut to_process): (Vec<_>, Vec<_>) =
        names.iter().partition(|(_, ts)| ts.is_none());

    let mut actions = Vec::with_capacity(names.len());
    // ignored items are handled trivially and do not affect any retention counts.
    for (name, _) in ignored {
        actions.push((name.as_str(), Action::Ignore));
    }

    let mut bins = RetentionBins::new(keep);
    to_process.sort();
    for (name, timestamp) in to_process.iter().rev() {
        let timestamp = timestamp.unwrap();
        actions.push((name.as_str(), bins.can_retain(timestamp)));
    }
    actions
}

fn main() -> Result<()> {
    let opts = Opt::from_args();

    let keep = RetentionRules::from_opts(&opts);
    if keep.is_empty() {
        return Err(anyhow!("No retention rules specified. At least one of --keep-{hourly,daily,weekly,monthly,yearly,within} must be specified with non-0 count, or all names would be pruned."));
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

    use chrono::{Duration, NaiveDate, NaiveDateTime, Timelike};

    use super::*;

    #[test]
    fn parse_retain_within() {
        assert!("0".parse::<RetainWithin>().is_err());
        assert!("1z".parse::<RetainWithin>().is_err());
        assert!("z".parse::<RetainWithin>().is_err());
        assert!("".parse::<RetainWithin>().is_err());
        for (units, mnemonics) in &[
            (TimeUnits::Hours, ["h", "H"]),
            (TimeUnits::Days, ["d", "D"]),
            (TimeUnits::Weeks, ["w", "W"]),
            (TimeUnits::Months, ["m", "M"]),
            (TimeUnits::Years, ["y", "Y"]),
        ] {
            for mnemonic in mnemonics {
                assert!(format!("0{}", mnemonic).parse::<RetainWithin>().is_err());
                assert!(format!("-1{}", mnemonic).parse::<RetainWithin>().is_err());
                assert!(format!("1.23{}", mnemonic).parse::<RetainWithin>().is_err());
                let good_parse = format!("1{}", mnemonic).parse::<RetainWithin>();
                let good_parse = good_parse.expect("should have parsed successfully");
                assert_eq!(good_parse.time_units, *units);
                assert_eq!(good_parse.count, 1);
            }
        }
    }

    #[test]
    fn default_timestamps() {
        let name = "foo-2020-06-27-11-12-13".to_string();
        let timestamp = NaiveDate::from_ymd(2020, 6, 27).and_hms(11, 12, 13);
        let parsed = parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, name.clone());
        assert_eq!((name, Some(timestamp)), parsed)
    }

    #[test]
    fn alternate_timestamps() {
        let name = "foo-2020-06-27-11-12".to_string();
        let timestamp = NaiveDate::from_ymd(2020, 6, 27).and_hms(11, 12, 0);
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

    fn test_rules(keep: RetentionRules, expected: Vec<(String, Action)>) {
        let parsed = expected
            .iter()
            .map(|(n, _)| parse_timestamp("foo-".len(), DEFAULT_TIMESTAMP_FORMAT, n.clone()))
            .collect::<Vec<_>>();

        let actions = prune(keep, &parsed[..]);
        let actions = actions.into_iter().collect::<HashMap<_, _>>();

        let len = expected.len();
        for (i, (n, expected)) in expected.into_iter().enumerate() {
            assert_eq!(
                actions[n.as_str()],
                expected,
                "case {}/{}: {}",
                i + 1,
                len,
                n
            );
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(1),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(2),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Unlimited,
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(1),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(2),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Unlimited,
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(1),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(2),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Unlimited,
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(1),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(2),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Unlimited,
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(1),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(2),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Unlimited,
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(1),
            daily: RetentionCount::Count(1),
            weekly: RetentionCount::Count(1),
            monthly: RetentionCount::Count(1),
            yearly: RetentionCount::Count(1),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
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
        ];

        let keep = RetentionRules {
            within: None,
            hourly: RetentionCount::Count(2),
            daily: RetentionCount::Count(2),
            weekly: RetentionCount::Count(2),
            monthly: RetentionCount::Count(2),
            yearly: RetentionCount::Count(2),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
    }

    fn generate_timestamp_name(prefix: &str, timestamp: NaiveDateTime) -> String {
        format!("{}{}", prefix, timestamp.format(DEFAULT_TIMESTAMP_FORMAT))
    }

    trait NaiveDateTimeExt {
        fn at_min(&self, min: u32) -> NaiveDateTime;
        fn add_mins(&self, mins: i64) -> NaiveDateTime;
        fn add_hours(&self, hours: i64) -> NaiveDateTime;
        fn add_days(&self, days: i64) -> NaiveDateTime;
        fn add_weeks(&self, weeks: i64) -> NaiveDateTime;
        fn add_months(&self, months: i64) -> NaiveDateTime;
        fn add_years(&self, years: i64) -> NaiveDateTime;
    }

    impl NaiveDateTimeExt for NaiveDateTime {
        fn at_min(&self, min: u32) -> NaiveDateTime {
            self.date().and_hms(self.hour(), min, self.second())
        }
        fn add_mins(&self, mins: i64) -> NaiveDateTime {
            *self + Duration::minutes(mins)
        }
        // Implemented in terms of `TimeUnits` to maintain consistent logic for e.g. months = 31
        // days.
        fn add_hours(&self, hours: i64) -> NaiveDateTime {
            *self + TimeUnits::Hours.duration(hours)
        }
        fn add_days(&self, days: i64) -> NaiveDateTime {
            *self + TimeUnits::Days.duration(days)
        }
        fn add_weeks(&self, weeks: i64) -> NaiveDateTime {
            *self + TimeUnits::Weeks.duration(weeks)
        }
        fn add_months(&self, months: i64) -> NaiveDateTime {
            *self + TimeUnits::Months.duration(months)
        }
        fn add_years(&self, years: i64) -> NaiveDateTime {
            *self + TimeUnits::Years.duration(years)
        }
    }

    fn test_within_only(within: RetainWithin) {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            (
                generate_timestamp_name("foo-", within.cutoff.add_mins(1)),
                Action::Retain(RetainedBy::Within(within)),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_mins(-1)),
                Action::Remove,
            ),
        ];

        let keep = RetentionRules {
            within: Some(within),
            hourly: RetentionCount::Count(0),
            daily: RetentionCount::Count(0),
            weekly: RetentionCount::Count(0),
            monthly: RetentionCount::Count(0),
            yearly: RetentionCount::Count(0),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
    }

    fn retain_from(time_units: TimeUnits, count: u32) -> RetainWithin {
        let cutoff = NaiveDate::from_ymd(2019, 6, 30).and_hms(18, 30, 30)
            - time_units.duration(count as i64);
        RetainWithin {
            cutoff,
            time_units,
            count,
        }
    }

    #[test]
    fn retain_within_hours_only() {
        test_within_only(retain_from(TimeUnits::Hours, 2));
    }

    #[test]
    fn retain_within_days_only() {
        test_within_only(retain_from(TimeUnits::Days, 2));
    }

    #[test]
    fn retain_within_weeks_only() {
        test_within_only(retain_from(TimeUnits::Weeks, 2));
    }

    #[test]
    fn retain_within_months_only() {
        test_within_only(retain_from(TimeUnits::Months, 2));
    }

    #[test]
    fn retain_within_years_only() {
        test_within_only(retain_from(TimeUnits::Years, 2));
    }

    fn test_within(within: RetainWithin) {
        let expected = vec![
            ("foo-not-a-timestamp".to_string(), Action::Ignore),
            ("foo-2020-_6-27-11-12-13".to_string(), Action::Ignore),
            (
                generate_timestamp_name("foo-", within.cutoff.add_mins(1)),
                Action::Retain(RetainedBy::Within(within)),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_hours(-2).at_min(30)),
                Action::Retain(RetainedBy::Hourly),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_hours(-2).at_min(29)),
                Action::Retain(RetainedBy::Daily),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_hours(-3).at_min(30)),
                Action::Retain(RetainedBy::Hourly),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_hours(-3).at_min(29)),
                Action::Retain(RetainedBy::Weekly),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_hours(-3).at_min(28)),
                Action::Retain(RetainedBy::Monthly),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_hours(-3).at_min(27)),
                Action::Retain(RetainedBy::Yearly),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_hours(-3).at_min(26)),
                Action::Remove,
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_days(-1).at_min(30)),
                Action::Retain(RetainedBy::Daily),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_days(-1).at_min(29)),
                // The date math works out such that this roll back falls into a new week for the
                // Monthly case.
                if TimeUnits::Months == within.time_units {
                    Action::Retain(RetainedBy::Weekly)
                } else {
                    Action::Remove
                },
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_weeks(-1).at_min(30)),
                if TimeUnits::Months != within.time_units {
                    Action::Retain(RetainedBy::Weekly)
                } else {
                    Action::Remove
                },
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_weeks(-2).at_min(30)),
                Action::Remove,
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_months(-1).at_min(30)),
                Action::Retain(RetainedBy::Monthly),
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_months(-2).at_min(30)),
                Action::Remove,
            ),
            (
                generate_timestamp_name("foo-", within.cutoff.add_years(-1).at_min(30)),
                Action::Retain(RetainedBy::Yearly),
            ),
            (
                generate_timestamp_name(
                    "foo-",
                    within.cutoff.add_years(-1).at_min(30).add_mins(-1),
                ),
                Action::Remove,
            ),
        ];

        let keep = RetentionRules {
            within: Some(within),
            hourly: RetentionCount::Count(2),
            daily: RetentionCount::Count(2),
            weekly: RetentionCount::Count(2),
            monthly: RetentionCount::Count(2),
            yearly: RetentionCount::Count(2),
        };
        assert!(!keep.is_empty());
        test_rules(keep, expected);
    }

    #[test]
    fn retain_within_hours() {
        test_within(retain_from(TimeUnits::Hours, 2));
    }

    #[test]
    fn retain_within_days() {
        test_within(retain_from(TimeUnits::Days, 2));
    }

    #[test]
    fn retain_within_weeks() {
        test_within(retain_from(TimeUnits::Weeks, 2));
    }

    #[test]
    fn retain_within_months() {
        test_within(retain_from(TimeUnits::Months, 2));
    }

    #[test]
    fn retain_within_years() {
        test_within(retain_from(TimeUnits::Years, 2));
    }
}
