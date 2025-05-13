COQPROJECT="_CoqProject"
COQFILES=$(grep '[.]v' $COQPROJECT)
coqdoc -d docs/ \
       -g handwritten/*.v \
       -utf8 \
       -R handwritten KeyScheduleTheorem \
       -R fextraction BertieExtraction \
       --table-of-contents \
       --multi-index $COQFILES
