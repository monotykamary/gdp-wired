3 proven, 2 refuted, 0 unknown, 8 not read or no result

| Engine | Language | Kind | Law | Verdict | Time | Written (comment lines + gdp.toml lines) |
| --- | --- | --- | --- | --- | --- | --- |
| manuelinfosec | Go | limit order book | OrderBook: the book no longer crosses | not read (OrderBook.go:62:5: github.com/shopspring/decimal.NewFromString: the value of github.com/shopspring/decimal.NewFromString, other code left out compared with a ni) | 0.0 s | 1 + 0 |
| mesa-clear | Python | order book (continuous double auction) | — | no result (the prover was killed: out of memory) | — | 2 + 3 |
| mesa | Python | order book (continuous double auction) | OrderBook: the best bid fills | proven | 10.9 s | 5 + 3 |
| mesa | Python | order book (continuous double auction) | OrderBook: the best ask fills | proven | 9.3 s | 5 + 3 |
| mesa | Python | order book (continuous double auction) | OrderBook: a fill crosses | proven | 8.6 s | 5 + 3 |
| mesa | Python | order book (continuous double auction) | OrderBook: the earliest to arrive at the best price fills | broken | 11.1 s | 5 + 3 |
| mesa | Python | order book (continuous double auction) | OrderBook: no agent trades with itself | broken | 11.8 s | 5 + 3 |
| microoptimus | Java | pre-trade risk checks | RiskManager: an approved order is within the order size limits | not read (RiskManager.java:61:34: OrderType.LIMIT: class (outside the subset)) | 0.0 s | 1 + 4 |
| pedernera | TypeScript | matching engine | MatchingEngine: fills never exceed the order | not read (matching-engine.ts:16:3: RestingOrder[]: an array of records (arrays of numbers, booleans and string unions are lists in the subset)) | 0.0 s | 1 + 0 |
| tpmullee | Python | matching engine | OrderBook: a cancelled order leaves the index | not read (engine.py:101:16: side.lower: a field of a str) | 0.0 s | 1 + 2 |
| zaranip | Python | matching engine | OrderBook: a cancelled order rests no more | not read (order_book.py:36:24: order.order_id: order_id, a field Order doesn't declare) | 0.0 s | 3 + 2 |
| zaranip | Python | matching engine | OrderBook: the book no longer crosses | not read (order_book.py:36:24: order.order_id: order_id, a field Order doesn't declare) | 0.0 s | 3 + 2 |
| zaranip | Python | matching engine | OrderBook: a fill takes no more than an order rests | not read (order_book.py:36:24: order.order_id: order_id, a field Order doesn't declare) | 0.0 s | 3 + 2 |
