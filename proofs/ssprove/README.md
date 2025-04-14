Generate patch file by first running extraction
```bash
./hax-driver.py extract-ssprove
```
in the root folder. Then running the following in the `proofs/ssprove/` folder
```bash
diff -x '*.aux' -x "*.glob" -x "*.vo" -x "*.vos" -ruN extraction/ fextraction/ > extraction.patch
```
we get the `extraction.patch` file. To apply the patch instead do
```bash
patch -ruN -d extraction/ < extraction.patch
rm -rf fextraction/
mv extraction/ fextraction/
```
