for i in Xlone_Via_Map Xlone_Clone_Clone  Xlone_All_Owners  Xlone_All_Fields Xlone_Field_Map; do echo $i; date; time nightly verify dfyconfig.toml  --filter-symbol=$i > M-$i-dump.txt; date;  done 
