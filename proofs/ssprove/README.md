Generate patch file by first running extraction
```bash
./hax-driver.py extract-ssprove
```
in the root folder. Then running the following in the `proofs/ssprove/` folder
```bash
diff -x '*.aux' -x "*.glob" -x "*.vo" -x "*.vos" -x "*.orig" -x "*.rej" -ruN extraction/ fextraction/ > extraction.patch
```
we get the `extraction.patch` file. To apply the patch instead do
```bash
patch -d extraction/ < extraction.patch
rm -rf fextraction/
mv extraction/ fextraction/
```
you might have to (re)generate the makefile to make it run
```bash
coq_makefile -f _CoqProject -o Makefile
```

# Versions
We are using `hax:main`, `ssprove:jasmin-coq.8.18.0`
