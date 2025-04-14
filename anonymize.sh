######################################
# Replace instances of Bertie/bertie #
######################################

rm -rf target/

find . -not -path "./.git/*" -type f -name '*Bertie*' | while read FILE ; do
    newfile="$(echo ${FILE} |sed -e 's/Bertie/T13/')" ;
    mv "${FILE}" "${newfile}" ;
done

find . -not -path "./.git/*" -type f -name '*bertie*' | while read FILE ; do
    newfile="$(echo ${FILE} |sed -e 's/bertie/t13/')" ;
    mv "${FILE}" "${newfile}" ;
done

find . -not -path "./.git/*" -type f -exec sed -i 's/Bertie/T13/g' {} \;
find . -not -path "./.git/*" -not -path "./tests/*" -type f -exec sed -i 's/bertie/t13/g' {} \;

find ./tests -name "*.rs" -type f -exec sed -i 's/bertie/t13/g' {} \;
find ./tests -name "*.sh" -type f -exec sed -i 's/bertie/t13/g' {} \;

find ./Cargo.toml -type f -exec sed -i 's/t13-libs/bertie-libs/g' {} \;

rm Cargo.lock

grep -rI bertie
grep -rI Bertie
find . -type f -name '*bertie*'
find . -type f -name '*Bertie*'
