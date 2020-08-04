# rdedup-prune

Prunes `rdedup` names that do not match the given criteria. Names must be in a format matching
`<prefix><timestamp>` where timestamp is formatted as yyyy-mm-dd-HH-MM-SS. Alternate timestamp
formats may be specified with the `--timestamp-format` option.

Specifying a negative value for any of `--keep-{hourly,daily,weekly,monthly,yearly}` will result
in an unlimited number for that category. Specifying 0 disables the directive (the same as not
specifying the directive at all).

The `--keep-within` rule specifies an interval in which to keep all names, which do not count
towards any counts for the `--keep-{hourly,daily,weekly,monthly,yearly}` rules. Intervals are
specified as <count><unit>, where count must be a positive integer, and unit if one of:
  * h - hours
  * d - days
  * w - weeks
  * m - months (31 days)
  * y - years (365 days)

For example `--keep-within 1d -h 2 -d 2` would keep all names within a day, the most recent
2 hourly names prior to a day ago, and the most recent daily names prior to a day ago.
