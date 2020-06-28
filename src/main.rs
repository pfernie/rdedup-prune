#![deny(warnings, missing_debug_implementations, rust_2018_idioms)]

use std::{env, result::Result as StdResult};

use anyhow::anyhow;
use rdedup_lib;
use slog::{self, info, o, Drain};
use slog_async;
use slog_term;
use structopt::StructOpt;
use url;

#[derive(Debug, StructOpt)]
/// Prunes `rdedup` names that do not match the given criteria. Names must be in a format matching
/// `<prefix><timestamp>` where timestamp is formatted as yyyy-mm-dd-HH-MM-SS.
struct Opt {
    #[structopt(parse(from_occurrences), short = "v", long = "verbose")]
    /// Increase debugging level for general messages
    verbose: u32,
    #[structopt(parse(from_occurrences), short = "t", long = "verbose-timings")]
    /// Increase debugging level for timing messages
    verbose_timings: u32,
    #[structopt(short = "p", long = "prefix")]
    /// The prefix string for names to be pruned
    prefix: String,
    #[structopt(short = "n", long = "dry-run")]
    /// Dry-run only; do not prune any names
    dry_run: bool,
    #[structopt(short = "H", long = "keep-hourly")]
    /// Number of hourly archives to keep
    keep_hourly: Option<i32>,
    #[structopt(short = "d", long = "keep-daily")]
    /// Number of daily archives to keep
    keep_daily: Option<i32>,
    #[structopt(short = "w", long = "keep-weekly")]
    /// Number of weekly archives to keep
    keep_weekly: Option<i32>,
    #[structopt(short = "m", long = "keep-monthly")]
    /// Number of monthly archives to keep
    keep_monthly: Option<i32>,
    #[structopt(short = "y", long = "keep-yearly")]
    /// Number of yearly archives to keep
    keep_yearly: Option<i32>,
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

fn main() -> Result<()> {
    let opts = Opt::from_args();

    let log = create_logger(opts.verbose, opts.verbose_timings);

    let url = if let Some(uri) = env::var_os("RDEDUP_URI") {
        if env::var_os("RDEDUP_DIR").is_some() {
            Err(anyhow!(
                "Cannot specify both RDEDUP_DIR and RDEDUP_URI at the same time."
            ))?;
        }
        let uri = uri
            .to_os_string()
            .into_string()
            .map_err(|_| anyhow!("RDEDUP_DIR='{}' is not valid UTF-8", uri.to_string_lossy()))?;
        url::Url::parse(&uri)?
    } else if let Some(dir) = env::var_os("RDEDUP_DIR") {
        url::Url::from_file_path(&dir)
            .map_err(|_| anyhow!("URI parsing error: {}", dir.to_string_lossy()))?
    } else {
        Err(anyhow!("Repository location not specified"))?
    };

    let repo = rdedup_lib::Repo::open(&url, log)?;

    for name in repo.list_names()? {
        println!("{}", name);
    }

    Ok(())
}
