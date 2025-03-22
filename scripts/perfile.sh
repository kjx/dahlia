for i in *.dfy; do echo $i;  date;  time nightly verify  dfyconfig.toml --filter-position=$i >F-$i.dump.txt  ; done 
