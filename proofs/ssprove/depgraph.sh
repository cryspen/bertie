#!/usr/bin/env bash

# Adapt to macOS (brew install gsed)
SED=`which gsed 2>/dev/null || which sed`

fn_project=_CoqProject
fn_out="dependencies"
base_style="rounded,filled"
# Some categorical color schemes recognised by dot: pastel19, set312
# http://www.graphviz.org/doc/info/colors.html#brewer
color_scheme=pastel19
n_colors_max=9

function help_msg() {
    echo "`basename $0`: Print dependency graph for \"$fn_project\" according to coqdep."
    echo "Requires graphviz, coqdep, bash, and sed."
}
if ! [ -z $@ ] ; then
    help_msg ; exit 1
fi

( echo "digraph interval_deps {" ;
  echo 'node [shape=box, style="'$base_style'", URL="https://SSProve.github.io/ssprove/\N.html", colorscheme='$color_scheme'];';
  coqdep -vos -dyndep var -f $fn_project |
      # rewrite prefixes
      $SED -f <($SED -nr 's/^ *-Q +(\S+) +(\S+)/s,\1,\2,g/p' < _CoqProject) |
      # turn '/' into '.' ,
      $SED -n -e 's,/,.,g' \
          `# keep lines with [src].vo : [x].v [dst]* , drop [x].v` \
          -e 's/[.]vo.*: [^ ]*[.]v//p' |
      {
          declare -A colmap
          while read src dst; do
              # pick a color number based on the src node name
              #prefix=$(echo "$src" | $SED -e 's,SSProve.,,g' -e '/^[^\.]*$/s/.*/__/' -e '/\./s/\..*//')
              #prefix=$(echo "$src" | $SED -e 's,SSProve.,,g' -e '/^[^\.]*$/s/.*/__/' -e 's/\(.*\)\..*/\1/')
              #color=${colmap[$prefix]}
              #if [ -z "$color" ] ; then
              #    color=$(( ${#colmap[*]} + 1))
              #    color=$(( color < n_colors_max ? color : n_colors_max ))
              #    colmap[$prefix]=$color
              #fi
              color=$(echo "$src" | $SED -r \
					-e 's,handwritten.*,2,' \
					-e 's,fextraction.*,3,' \
                                        -e 's,.*\..*,1,') # default
              echo "\"$src\" [fillcolor=$color];"
              for d in $dst; do
                  echo "\"$src\" -> \"${d%.vo*}\" ;"
              done
          done;
      }
  echo "}" ) |
    # transitively reduce graph
    tred |
    # double border around modules without further prerequisites
    gvpr -c 'N[outdegree == 0]{shape="doubleoctagon"}' |
    # fat border around modules without clients
    gvpr -c 'N[indegree == 0]{penwidth=3}' > $fn_out.dot

dot -T svg $fn_out.dot > $fn_out.svg
# dot -T png $fn_out.dot > $fn_out.png
# dot -T cmap $fn_out.dot | $SED -e 's,>$,/>,' > $fn_out.map
