for i in *.dfy; do echo $i;  date;  time nnightly verify  dfyconfig.toml --filter-position=$i >F-$i.dump.txt  ; done 
