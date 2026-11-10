// Loaded before the replay's imports, so wall accounting includes module load.
;(globalThis as {trackMWallStart?:number}).trackMWallStart=performance.now()
