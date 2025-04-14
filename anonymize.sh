rm -rf assets/
rm -rf target/
rm -f CODEOWNERS
rm -f SECURITY.md
rm -f CODE_OF_CONDUCT.md
rm -f util/top1m.txt
rm -rf .github/ISSUE_TEMPLATE
rm -rf CLA.md

### ACKNOWLEDGEMENTS

find . -not -path "./.git/*" -type f -exec sed -i -e '/assets/d' {} \;
find ./README.md -not -path "./.git/*" -type f -exec sed -i -e '/cryspen/d' {} \;



# find . -not -path "./.git/*" -type f -exec sed -i -e '/ACKNOWLEDGEMENTS/d' {} \;
# find . -not -path "./.git/*" -type f -exec sed -i -e '/Cryspen/d' {} \;
find . -not -path "./.git/*" -type f -exec sed -i -e '/Inria/d' {} \;


######################################
# Replace instances of t13/t13 #
######################################

find . -not -path "./.git/*" -type f -iname '*t13*' | while read FILE ; do
    newfile="$(echo ${FILE} |sed -e 's/t13/T13/i')" ;
    mv "${FILE}" "${newfile}" ;
done

find . -not -path "./.git/*" -not -path "./tests/*" -type f -exec sed -i 's/t13/t13/gi' {} \;
find ./tests -name "*.md" -type f -exec sed -i 's/t13/t13/gi' {} \;
find ./tests -name "*.rs" -type f -exec sed -i 's/t13/t13/gi' {} \;
find ./tests -name "*.sh" -type f -exec sed -i 's/t13/t13/gi' {} \;

find ./Cargo.toml -type f -exec sed -i 's/t13-libs/t13-libs/g' {} \;

rm Cargo.lock

### Checks

grep -riI t13 --exclude-dir=.git
grep -riI cryspen --exclude-dir=.git
grep -riI inria --exclude-dir=.git
grep -riI "Karthikeyan" --exclude-dir=.git
grep -riI "Karthikeyan Bhargavan" --exclude-dir=.git
find . -type f -iname '*t13*'
