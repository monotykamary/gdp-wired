#!/usr/bin/env bash
set -euo pipefail
src="$1"; dest=$(mktemp -d "$HOME/track-m-s18-receipts-XXXXXX")
tar -czf "$dest/receipts.tar.gz" -C "$src" .
bun -e 'import{readFileSync,writeFileSync}from"node:fs";import{createHash}from"node:crypto";const dir=process.argv[1],b=readFileSync(dir+"/receipts.tar.gz"),s=b.toString("base64"),size=200000;let parts=0;for(let i=0;i<s.length;i+=size)writeFileSync(dir+"/"+(parts++)+".txt",s.slice(i,i+size));const m={artifact:"track-m-tar-v1",dir,format:"tar.gz",parts,bytes:b.length,sha256:createHash("sha256").update(b).digest("hex")};writeFileSync(dir+"/manifest.json",JSON.stringify(m));console.log(JSON.stringify(m))' "$dest"
