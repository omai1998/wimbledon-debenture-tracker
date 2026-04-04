# Wimbledon Debenture Tracker

Tracks Wimbledon debenture ticket prices from:
- Wimbledon Debenture Holders (wimbledondebentureholders.com)
- Dowgate Capital

## Data

- `wimbledon_debentures.db` - SQLite database with all listings and price history
- `wimbledon_analysis.csv` - Master log export
- `wimbledon_daily_snapshots.csv` - Time-series snapshots

## Features

- **Listing tracking**: Unique hash for each ticket to track across scrapes
- **Price change detection**: Records price increases/decreases
- **Sold inference**: Marks listings as disappeared (likely sold) when they vanish
- **Time on market**: Tracks hours since first seen

## Automation

Runs every 2 hours via GitHub Actions. Manual trigger available in Actions tab.

## Local Development

```bash
pip install -r requirements.txt
python wimbledon_tracker.py
```

## Query Examples

```sql
-- Price changes
SELECT court, round, previous_price_gbp, price_gbp, price_direction
FROM wimbledon_master_log WHERE price_direction IS NOT NULL;

-- Listings that sold (disappeared)
SELECT court, round, price_gbp, last_seen
FROM wimbledon_master_log WHERE disappeared = 1;

-- Price trends for a specific day
SELECT scrape_date, price_gbp FROM daily_snapshots
WHERE match_day = 20260712 ORDER BY scrape_ts;
```
