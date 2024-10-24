method Klone_Via_Map(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //entry point for Klone - clones a according to map m'
  //call with m' empty
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 20 //Klone_Via_Map

  requires m'.calid()
  requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap)

//  //FROMHERE 
//   ensures  m.calid()
// 
//   ensures  a in m.m.Keys
//   ensures  m.m[a] == b
//   ensures  b in m.m.Values
//   ensures  COK(b,m.oHeap+m.ns)
// 
//   //should I package this up - as aw twostate or a onestate?
//   ensures  mapLEQ(m'.m,m.m)
//   ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
//   ensures  m.from(m')
// 
//   ensures  m.o == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns
//   //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures  klonVMapOK(m.m)
//   ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   // should we say something about b.AMFO?  b.AMFO <= m.m.Values? por again m.hasV(b)?
//   // m.key(a)?  m.val(a)???
//   // should decided whether to do this with AMFOs or owners
//   // and don one one...
//   ensures  m.from(m')
//   ensures b.AMFO == mapThruKlon(a.AMFO, m)
// 
//   // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
//   ensures  unchanged(a)
//   ensures  unchanged(m'.oHeap)
//   ensures  unchanged(m'.ns)
// 
//   ensures b.fieldModes == a.fieldModes
// 
// //TOHERE

  //  ensures  fresh(b)
  //modifies m'[a]
  //  modifies m'.ns`fields //argh. pity so wide
  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  // modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  modifies {} // only modifes objecst allocated after this point?
{
  m := m';

  print "CALL Klone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";
  print "VARIANT CVM ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 20, "\n";

  assert COKSTART: COK(a, m.oHeap);

  print "Klone_Via_Map started on:", fmtobj(a), "\n";

  //if already in hash table - return it and be done!
  //not sure why this takes sooo long compared to other
  if (a in m.m.Keys) {

            b := m.m[a];   //what no 'putooutside'

            print "RETN Klone_Via_Map: ", fmtobj(a)," already cloned,  returning ",fmtobj(b), "\n";

            return;
  } // a in m.Keys, already cloned

///case analysis...
  if (outside(a,m.o)) {
    print "Klone_Via_Map ", fmtobj(a), " is really outside ", fmtobj(m.o), "so maps to itself (share not clone)\n";

      print "Hey Baby let's CLONE Outside\n";

      b := a;


      print "Yay babhy hyou got that done\n";


  print "about to putOutside\n";



print "returnin' from the outsidee case\n";

    // assert a !in m'.m.Keys ==> b !in m'.ns;   //KJX sure about this?

    return;  //we may as well just return here.
             //we've done all we need to do.  I think.

  }///END OF THE OUTSIDE CASE
  else
  { //start of the Inside case
print "start of the Inside case\n";
      print "Klone_Via_Map owners:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";

      b, m := Klone_Klone_Klone(a, m);

      // assert a !in m'.m.Keys ==> b !in m'.ns;  }  //end of inside case
print "end of the Inside case\n";

  } //end of inside case

  /////////////////////////////////////////////////////////////// 
  //tidying up after the cases..

  //  }
  print "RETN Klone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

}





method Klone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)
  //clone all fields a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10 //Klone_All_Fields
// 
//   requires MPRIME: m'.calid()
//   requires COK(a, m'.oHeap)
//   requires COK(b, m'.oHeap+m'.ns)
// 
//   requires b.fields.Keys == {}
// 
//   requires a.fields.Keys <= a.fieldModes.Keys
//   requires a.fieldModes == b.fieldModes
// 
// 
//   requires a in m'.oHeap
//   requires a in m'.m.Keys
// 
//   requires b in m'.m.Values
//   requires b in m'.ns
//   requires (a in m'.m.Keys) && m'.m[a] == b
//   requires m'.o    in m'.oHeap
//   requires m'.m.Keys   <= m'.oHeap
// 
//   requires a.AMFO <= m'.m.Keys  //seems weird but we are populating m, right...
//  
//   
// 
//   ensures  m.calid()
//   ensures  old(m'.calid())
//   ensures  klonVMapOK(m.m)
//   ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
// 
//   ensures  b.fields.Keys == a.fields.Keys
// 
//   ensures  a in m.m.Keys
//   ensures  (a in m.m.Keys) && m.m[a] == b



//   ensures  b in m.m.Values
// 
//   ensures  mapLEQ(m'.m,m.m)
// 
//   ensures  CallOK(m.oHeap)
//   ensures  COK(a, m.oHeap)
//   ensures  COK(b, m.oHeap+m.ns)
//   ensures  CallOK(m.m.Values, m.oHeap+m.ns)
//   ensures  CallOK(m.ns, m.oHeap+m.ns)
// 
//   ensures  m.o     == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns    >= m'.ns
//   ensures  m.m.Keys    <= m.oHeap
// 
//   ensures a.fieldModes == b.fieldModes
//   ensures b.fields.Keys == a.fields.Keys
// 
//   ensures  unchanged(a)
//   ensures  unchanged(m'.oHeap)
//   ensures  unchanged(m'.ns - {b})  //will this work?
// 
//   ensures  forall x <- (m.m.Values - {b}) :: old(allocated( x )) ==> unchanged( x ) //duesb;t veruft....

  //  modifies (set o : Object | o !in m'.oHeap)`fields
  // modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns?
  modifies b`fields   ///GGRRR
{
  m := m';

  print "CALL Klone_All_Fields: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

  print "VARIANT CAF ", |(m'.oHeap - m'.m.Keys +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";
  print "<<<<<<<<<<<\n";
  print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
  print "<<<<<<<<<<<\n";


  //START OF FIELDS…

  print "<<<<<<<<<<<\n";
  printmapping(m.m);
  print "<<<<<<<<<<<\n";

  var ns : seq<string> := set2seq(a.fields.Keys);

  print "Klone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(ns), "\n";




  var rm := m;


  for i := 0 to |ns|

  {

    var n : string := ns[i];
    assume n in a.fields;
    var ofv : Object := a.fields[n];

    assert n !in seq2set(ns[..i]);

    print "  TLOOP  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "  TLOOP  (recurse on field ",n,")\n";
    print "  TLOOP m:", |m.oHeap - m.m.Keys|, " m':", |m'.oHeap - m'.m.Keys|, "\n";
    print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
    print "  TINV                ", ns[..i], "\n";
    print "  TLOOPINV            ",seq2set(ns[..i]),"\n";


    print "VARIANT*CAF ", |(m'.oHeap - m'.m.Keys +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";



    var OLDFLDS := b.fields.Keys;


    var v_caf := ((m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);
    var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Klone_Field_Map

    print "v_caf ", v_caf, "\n";
    print "v_cfm ", v_cfm, "\n";


    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) >  (m.oHeap - m.m.Keys +{a}), "\n";
    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) == (m.oHeap - m.m.Keys +{a}), "\n";

    rm := Klone_Field_Map(a,n,b,m);

    m := rm;

  } //end of loop

  print "RETN Klone_All_Fields done ", fmtobj(a), "\n";

  return;
}
//end Klone_All_Fields



  method   Klone_Klone_Klone(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //actually does the clone....
  // was the old Klone_Inside_Heap
//  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 
  decreases (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 15 


  //this case
  requires inside(a,m'.o)
  requires a !in m'.m.Keys

  //all Klone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)
// 
//   ensures  m.calid()
//   ensures  a in m.m.Keys
//   ensures  b in m.m.Values
//   ensures  a in m.m.Keys && m.at(a) == b
// //  ensures  b in m.ns
// //  ensures  COK(b, m.oHeap+m.ns)
// 
//   //should I package this up - as aw twostate or a onestate?
//   //it;s about clonbamps, so clonmapLEQ or clonmapEXTENDS
//   ensures  mapLEQ(m'.m,m.m)
//   ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
//   ensures  m.o == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns
//   //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   ensures old(m'.calid())
//   ensures m.from(m')
// // 
// //   //ensures b.AMFO == set x <- a.AMFO :: m.m[x]
// // 
//   ensures b.fieldModes == a.fieldModes
//   //   ensures b.fields.Keys == a.fields.Keys

  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  //modifies (set o : Object)`fields
  // ensures a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?   //Cline INsinside heap
  // ensures b in m'.ns ==> a in m'.m.Keys
  modifies {}
{ //clone inside heap
  m := m';


  print "Klone_Klone_CLone of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CIH ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

  
  print "Klone_Klone_CLone ", fmtobj(a), " calling Klone_All_Owners", fmtown(a.owner) ,"\n";

  var rm := Klone_All_Owners(a, m);

assume a.owner <= rm.m.Keys;
  var rowner := mapThruKlon(a.owner, rm);

assume a.allExternalOwners() <= rm.m.Keys;
  var rAMXO  := mapThruKlon(a.allExternalOwners(),  rm);

  print "Klone_Klone_CLone ", fmtobj(a), " Klone_All_Owners RETURNS ", fmtown(rowner) ,"\n";

  if (a in rm.m.Keys) {

    print "Klone_Klone_CLone ", fmtobj(a), " already cloned: abandoning ship!!\n";


    m := rm;
    assume rm.calid();
    assume a in rm.m.Keys;
    b := rm.at(a);

    return;
  } // a in rm.m.Keys - i.e. randomly done while cloning owners

  print "Klone_Klone_CLone ", fmtobj(a), " have rowner ", fmtown(rowner) ," self not yet cloned\n";

var rrm := rm; //KJX THIS IS EVIL, should clean up and get rid of rrm completel6.

print "Klone_Klone_Klone ", fmtobj(a), " boodle boodle boodle\n";

  var context := rrm.oHeap+rrm.ns;    ///why haul ns in here??? --- cos this the owners for the clone!  - the clowners!


print "CALLING MAKE...";
  b := new Object.fake(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick);
print "BACK FROM MAKE with ",fmtobj(b),"\n";


assume klonCanKV(rrm, a, b);
  var xm := rrm.putin(a,b);

  print "Klone_CLone_Klone map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";


print "FUCKFUCKFUCK  Klone_All_Fields commented out\n";


   m := Klone_All_Fields(a,b, xm);



  print "Klone_Klone_CLone of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";
}













method Klone_Field_Map(a : Object, n : string, b : Object, m' : Klon)
  returns (m : Klon)
  //clone field a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 //Klone_Field_Map
// 
//   requires MPRIME: m'.calid()
//   requires COK(a, m'.oHeap)
//   requires COK(b, m'.oHeap+m'.ns)
// 
//   requires n  in a.fields.Keys
//   requires n !in b.fields.Keys
// 
//   requires n  in a.fieldModes
//   requires n  in b.fieldModes
//   requires a.fieldModes == b.fieldModes
//   requires FLDMODZ: a.fieldModes == b.fieldModes
// 
// 
//   requires a in m'.oHeap
//   requires a in m'.m.Keys
//   requires a.AMFO <= m'.m.Keys //KJX should be part of some invariant
// 
//   requires b in m'.ns
//   requires b in m'.m.Values
//   requires b.AMFO <= m'.m.Keys //KJX should be part of some invariant - also 
//   
// 
//   requires (a in m'.m.Keys) && m'.m[a] == b
//   requires m'.o    in m'.oHeap
//   requires m'.m.Keys   <= m'.oHeap
// 
// 
//     //not sure why I'd need this..
//   requires forall n <- b.fields :: (n in b.fieldModes) &&
//                                    AssignmentCompatible(b, b.fieldModes[n], b.fields[n])
// 
//   //consequently
//   requires refOK(a, a.fields[n])
// 
// 
// 
//   ensures  b.fields.Keys == old(b.fields.Keys) + {n}
//   ensures  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys)
//   ensures  m.calid()
//   ensures  old(m'.calid())
// 
// 
//   ensures  a in m.m.Keys
//   ensures  (a in m.m.Keys) && m.m[a] == b
// 
//   ensures  n in b.fields
//   ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]
// 
//   ensures  b in m.m.Values
// 
//   ensures  mapLEQ(m'.m,m.m)
// 
//   ensures  CallOK(m.oHeap)
//   ensures  COK(a, m.oHeap)
//   ensures  COK(b, m.oHeap+m.ns)
//   ensures  CallOK(m.m.Values, m.oHeap+m.ns)
//   ensures  CallOK(m.ns, m.oHeap+m.ns)
// 
//   ensures  m.o     == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns    >= m'.ns
//   ensures  m.m.Keys    >= m'.m.Keys
//   ensures  m.m.Values    >= m'.m.Values
//   ensures  m.m.Keys    <= m.oHeap
// 
// 
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys // shoulnd't that be requires
// 
//   ensures old(m'.calid())
//   ensures m.from(m')
// 
//   ensures a.fieldModes == b.fieldModes
// 
//   ensures  unchanged(a)
//   ensures  unchanged(m'.oHeap)
//   ensures  unchanged(m'.m.Values - {b})
//   ensures  unchanged(m'.m.Keys)

  // ensures  unchanged(m'.ns - {b})  //will this work?

  modifies b`fields
{
  m := m';


  var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Klone_Field_Map

print "CALL Klone_Field_Map ", fmtobj(a), " «", n, "»\n";

  print "VARIANT CFM ", |(m'.oHeap - m'.m.Keys)+{a}|, " ", |a.AMFO|, " ", |(a.fields.Keys - b.fields.Keys - {n})|, " ", 10, "\n";

  var onb := m.ns - {b};
  var ctx := (m.oHeap+m.ns);

assume n in a.fields;
assume COK(a,m.oHeap);
assume CallOK(m.oHeap);

  var ofv := COKat(a,n,m.oHeap);

assume m.calid();

  var rfv, rm := Klone_Via_Map(ofv, m);

  m := rm;

  b.fields := b.fields[n := rfv];
  
} //end Klone: /_Field_Map





method Klone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
  //adds all thers owners of a into the map
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 12
// 
//   requires a !in m'.m.Keys //mustn't have cloned a yet...
//   requires COK(a, m'.oHeap)
//   requires m'.calid()
// 
//   ensures  m.calid()
//   //ensures  a !in m.m.Keys //can't ensures this cos an onwer could have a pointer to "a"
// 
//   ensures m.from(m')
//   ensures a.owner <= m.m.Keys
//   ensures a.allExternalOwners() <= m.m.Keys
  modifies {}
{
  var rm := m';
  var b : Object;  //do we care..

  var xm := rm;

  var xo : Object;
  var rr : Object;
  var oldmks  : set<Object>;  //dont fucking ask
  var oldmok :=  false;

  var MX := a.owner - xm.m.Keys;

  while ((MX != {}) && (a !in xm.m.Keys))
    decreases MX
    {
    xo :| xo in MX;

    MX := MX - {xo};

    assume xm.calid();
    assume xo in xm.oHeap; 
    assume COK(xo, xm.oHeap);
    
    rr, rm := Klone_Via_Map(xo, xm);

    if (a in rm.m.Keys) {
      m := rm;
      b := m.m[a];
    }  // if a is in m.Keys after clone -- if it got added magically...

    MX := MX - rm.m.Keys;
    oldmks := xm.m.Keys;
    oldmok := true;
    xm := rm;
  } // end loop MX

 m := xm;
}




