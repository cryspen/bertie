rm -rf assets/
rm -rf target/
rm -f CODEOWNERS
rm -f SECURITY.md
rm -f CODE_OF_CONDUCT.md
rm -f util/top1m.txt
rm -rf .github/ISSUE_TEMPLATE
rm -rf CLA.md
rm -rf bench.md
rm -rf LICENSE

### ACKNOWLEDGEMENTS

find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/assets/d' {} \;
find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/cryspen/d' {} \;

find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/PUBLICATIONS/d' {} \;
find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/a number of prior/d' {} \;
find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/Some of the most relevant/d' {} \;
find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/succinct, executable/d' {} \;
find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/Verified Models and Reference/d' {} \;
find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/A Messy State of the Union/d' {} \;

find . -not -path "./.git/*" -type f -exec sed -i -e '/reach out to Crypsen/d' {} \;

find . -not -path "./.git/*" -type f -exec sed -i -e '/LICENSE/d' {} \;
find . -not -path "./.git/*" -type f -exec sed -i -e '/licensed under/d' {} \;

# find . -not -path "./.git/*" -type f -exec sed -i -e '/ACKNOWLEDGEMENTS/d' {} \;
find . -not -path "./.git/*" -type f -exec sed -i -e '/The Bertie project./d' {} \;
find . -not -path "./.git/*" -type f -exec sed -i -e '/project tasks/d' {} \;
# find . -not -path "./.git/*" -type f -exec sed -i -e '/Cryspen/d' {} \;
find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/Inria/d' {} \;
find . -not -path "./.git/*" -type f -exec sed -i -e '/nlnet foundation/d' {} \;

find . -not -path "./.git/*" -type f -exec sed -i '/first authored Bertie/d' {} \;
find . -not -path "./.git/*" -type f -exec sed -i '/authors =/d' {} \;
find . -not -path "./.git/*" -type f -exec sed -i '/repository =/d' {} \;

######################################
# Replace instances of Bertie/bertie #
######################################

find . -not -path "./.git/*" -type f -name '*Bertie*' | while read FILE ; do
    newfile="$(echo ${FILE} |sed -e 's/Bertie/T13/')" ;
    mv "${FILE}" "${newfile}" ;
done

find . -not -path "./.git/*" -type f -iname '*bertie*' | while read FILE ; do
    newfile="$(echo ${FILE} |sed -e 's/bertie/t13/')" ;
    mv "${FILE}" "${newfile}" ;
done

find . -not -path "./.git/*" -not -path "./tests/*" -type f -exec sed -i 's/Bertie/T13/gi' {} \;
find . -not -path "./.git/*" -not -path "./tests/*" -type f -exec sed -i 's/bertie/t13/gi' {} \;
find ./tests -name "*.md" -type f -exec sed -i 's/bertie/t13/gi' {} \;
find ./tests -name "*.rs" -type f -exec sed -i 's/bertie/t13/gi' {} \;
find ./tests -name "*.sh" -type f -exec sed -i 's/bertie/t13/gi' {} \;

find ./Cargo.toml -type f -exec sed -i 's/bertie-libs/t13-libs/g' {} \;

rm Cargo.lock
cargo clean

### Checks

grep -riI bertie --exclude-dir=.git
grep -riI cryspen --exclude-dir=.git
grep -riI inria --exclude-dir=.git
grep -riI "Karthikeyan" --exclude-dir=.git
grep -riI "Karthikeyan Bhargavan" --exclude-dir=.git
find . -type f -iname '*bertie*'

rm -rf .git
rm -f anonymize.sh

