
const protoTypes : map<string, Mode> :=
      map["jat":= Evil]
         ["dat":= Evil]
         ["cat":= Evil]
         ["rat":= Evil]
         ["nxt":= Evil]
         ["eye":= Evil]
         ["kye":= Evil]
         ["lat":= Evil]
         ["fucker" := Evil]


method {:verify false} Main(s : seq<string>)
{
  print "Main()\n";

 if ((|s| > 1) && (|s[1]| > 0)) {

  print "xxx", (s[1][0]), "xxx\n";

   match (s[1][0]) {
     case '0' =>  Main0();
     case '1' =>  Main0();
     case '2' =>  Main2();
     case '3' =>  Main3();
     case '4' =>  Main4();
     case _ => {}
  }
  print "Exit, pursued by a bear\n";
 }
}


//{:verify false} //{:only}
method makeDemo() returns (t : Object, a : Object, os : set<Object>)
  ensures t in os
  ensures a in os
  ensures forall o <- os :: o.Ready()
  ensures forall o <- os :: o.AllOwnersAreWithinThisHeap(os)
  ensures forall o <- os :: o.AllOutgoingReferencesWithinThisHeap(os)
  ensures forall o <- os :: o.fieldModes == protoTypes
  ensures COK(a, os)
  ensures CallOK(os)
{

assert CallOK({}, {}) by { NothingShallComeOfNothing({}, {}); }

t := new Object.make(protoTypes, {}, {}, "t");
//   t
//   a      b c
//   d
//   e f g h

assert t.Ready();
assert COK(t, {t}) by { reveal COK(); }

// protoTypes 8-)
// cat dat eye fucker jat kye lat nxt rat/

assert t.AMFX == {};
assert forall o <- {t}, ooo <- o.AMFO :: o.AMFO >= ooo.AMFO;

assert CallOK({t},{t}) by { reveal COK(), CallOK(); }

a := new Object.make(protoTypes, {t}, {t}, "a");

var b := new Object.make(protoTypes, {t}, {t}, "b");

var c := new Object.make(protoTypes, {t}, {t}, "c");

reveal CallOK(), COK();
assert CallOK({a}, {t,a});
var d := new Object.make(protoTypes, {a}, {t,a}, "d");

assert CallOK({d}, {t,a,d});
var e := new Object.make(protoTypes, {d}, {t,a,d}, "e"); //we're gonna clone this one..?

assert CallOK({e}, {t,a,d,e});
var f := new Object.make(protoTypes, {e}, {t,a,d,e}, "f");

assert CallOK({f},  {t,a,d,e,f});
var g := new Object.make(protoTypes, {f},  {t,a,d,e,f},   "g");

assert CallOK({g}, {t,a,d,e,f,g});
var h := new Object.make(protoTypes, {g}, {t,a,d,e,f,g}, "h");

assert CallOK({g}, {t,a,d,e,f,g});
var i := new Object.make(protoTypes, {g}, {t,a,d,e,f,g}, "i");
assert CallOK({e}, {t,a,d,e,f,g,h});
var j := new Object.make(protoTypes, {e}, {t,a,d,e,f,g,h}, "j");
assert CallOK({e}, {t,a,d,e,f,g,h});
var k := new Object.make(protoTypes, {e}, {t,a,d,e,f,g,h}, "k");
assert CallOK({e},  {t,a,d,e,f,g,h});
var l := new Object.make(protoTypes, {e}, {t,a,d,e,f,g,h}, "l");


assert t.Ready();

assert a.Ready();
assert b.Ready();
assert c.Ready();
assert d.Ready();
assert e.Ready();
assert f.Ready();
assert g.Ready();
assert h.Ready();
assert i.Ready();
assert j.Ready();
assert k.Ready();
assert l.Ready();

os := {t,   a, b, c, d, e, f, g, h, i, j, k, l};

a.fields := map["eye":=d];
d.fields := map["lat":= e]["dat":=f]["cat":=g]["rat":= h];

assert COK(a,os);

assert d.AllFieldsAreDeclared();
assert d.AllFieldsContentsConsistentWithTheirDeclaration();
assert d.AllOutgoingReferencesAreOwnership(os);
assert d.AllOutgoingReferencesWithinThisHeap(os);
assert COK(d,os);

assert CallOK(os);

//////reveal Object.Ready();
assert t.AllOwnersAreWithinThisHeap(os);
assert a.AllOwnersAreWithinThisHeap(os);
assert b.AllOwnersAreWithinThisHeap(os);
assert c.AllOwnersAreWithinThisHeap(os);
assert d.AllOwnersAreWithinThisHeap(os);
assert e.AllOwnersAreWithinThisHeap(os);
assert f.AllOwnersAreWithinThisHeap(os);
assert g.AllOwnersAreWithinThisHeap(os);
assert h.AllOwnersAreWithinThisHeap(os);
assert i.AllOwnersAreWithinThisHeap(os);
assert j.AllOwnersAreWithinThisHeap(os);
assert k.AllOwnersAreWithinThisHeap(os);
assert l.AllOwnersAreWithinThisHeap(os);

assert forall o <- os :: (o.AllOwnersAreWithinThisHeap(os));


// print "\n=============================================================\n";
// ////
// var oq := [t,   a, b, c, d, e, f, g, h, i, j, k, l];
//
//   for i := 0 to |oq|
//     {
//       var o : Object := oq[i];
//
//       assert o.Ready();
//
//       printobject(o);
//     }
//    print "\n=============================================================\n";
//    print "\n\n";
}

// {:verify false} //{:only}
method {:verify false} Main0() {

  print "Main Test for loopback\n";

var t, a, os := makeDemo();

assert forall o <- os :: (o.Ready());
assert forall o <- os :: (o.AllOwnersAreWithinThisHeap(os));


print "|os| == ", |os|, "\n";

print "+++++++++++++\n";
print "original store (os)\n";
print "+++++++++++++\n";
printobjectset(os);
print "+++++++++++++\n";

print "done setup\n";

// printobj(a);
// printobjfields(a);

// print "here edgeset\n";
assert forall o <- os :: o.Ready();
// printedgeset(edges(os));
// print "done edgeset\n\n";

// printobj(d); printobjfields(d);
// printobj(e); printobjfields(e);

// print d.region,"\n";
// print e.region,"\n";

// assert !d.region.World?;
// assert !e.region.World?;

//assert isIsomorphicMappingOWNED(d, d, isomap, os);

// print "ISO ISO ISO\n";

// var ros := walkies(d, d, isomap, os);

// return;

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

print "about to Xlone a\n";

assert CallOK(os);
assert COK(a, os);
assert CallOK(a.owner,os) by { reveal COK(), CallOK(); }


assert forall o <- os :: (o.Ready());
assert forall o <- os :: (o.AllOwnersAreWithinThisHeap(os));

assert forall x <- os ::  x.AllOutgoingReferencesWithinThisHeap(os);


var m : Klon := seed(a, a.owner, os);

// var m := Klon(map[],    //m clonemap
//                a,       // o - object to be cloned / pivot / top object
//                a.AMFX,  // o_amfo AMFO of o
//                a.owner,  // c_owner - proposewd owner of clone
//                a.AMFX,   // c_amfx - AMFX of clone
//                os,      // oHeap
//                {}       // ns;
//               );

  assert m.calid();
  assert m.readyAll();
  assert allMapOwnersThruKlownOK(m);
  assert COK(a, m.oHeap);
  assert klonCanKV(m,a,a);

 var ra, rm := Xlone_Via_Map(a, m);

assert a in rm.m.Keys;
assert rm.from(m);
assert m.calid();
assert m.ownersInKlown(a);

print "+++++++++++++\n";
print "original store (os)\n";
print "+++++++++++++\n";
printobjectset(os);
print "+++++++++++++\n";
print "clones rm.Values - os\n";
print "+++++++++++++\n";
printobjectset(rm.m.Values - os);
print "+++++++++++++\n";
printmapping(rm.m);

print "\n\n\n\nwaiting...\\n\n";

var context : set<Object> := rm.oHeap + rm.ns;
assert os <= context;


// assume a in rm.m.Keys;
// assume a in context;
// assume m.m.Keys   <= context;
// assume m.m.Values <= context;

// var result : bool :=  jeSuisClone(a, rm, context);

var result : bool :=  istEinKlon(a, rm, context);


print "istEinKlon = ", result;

print "\n\n";

print "\nDone\n";
}
// end



method {:verify false} Main1() {

  print "Main Test for loopback\n";


var t, a, os := makeDemo();

print "|os| == ", |os|, "\n";

print "+++++++++++++\n";
print "original store (os)\n";
print "+++++++++++++\n";
printobjectset(os);
print "+++++++++++++\n";

print "done setup\n";

// printobj(a);
// printobjfields(a);

// print "here edgeset\n";
assert forall o <- os :: o.Ready();
// printedgeset(edges(os));
// print "done edgeset\n\n";

// printobj(d); printobjfields(d);
// printobj(e); printobjfields(e);

// print d.region,"\n";
// print e.region,"\n";k

// assert !d.region.World?;
// assert !e.region.World?;

//assert isIsomorphicMappingOWNED(d, d, isomap, os);

// print "ISO ISO ISO\n";

// var ros := walkies(d, d, isomap, os);

// return;

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

print "about to Clone a\n";

// var m : Klon := Klon(map[],    //m clonemap
//                a,       // o - object to be cloned / pivot / top object
//                a.AMFO,  // o_amfo AMFO of o
//                a.owner,  // c_owner - proposewd owner of clone
//                a.AMFX,   // c_amfx - AMFX of clone
//                os,      // oHeap
//                {}       // ns );
//               );


  var m : Klon := seed(a, a.owner, os);

//  var ra, rm := Clone_Via_Map(a, m);

print "NOT Cloning because Clone isn't linked\n";

var ra, rm := a, m;

// //
// //     m : Mapping,  //m : Mapping
// //     ks : set<Object>, //ks - set, keys of the mapping   (must be m.Keys, subset of oHeap)
// //     vs : set<Object>, //vs - set, values or the mapping (must be m.Values, subset of oHeap + ns)
// //     o : Object,  //o - Owner within which the clone is being performaed, in oHeap
// //     oHeap : set<Object>,  //oHeap - original (sub)heap contianing the object being cloned and all owners and parts
// //     ns : set<Object>)

print "+++++++++++++\n";
print "original store (os)\n";
print "+++++++++++++\n";
printobjectset(os);
print "+++++++++++++\n";
print "clones rm.Values - os\n";
print "+++++++++++++\n";
printobjectset(rm.m.Values - os);
print "+++++++++++++\n";
printmapping(rm.m);

print "\n\n\n\nwaiting...\\n\n";

var result : bool :=  istEinKlon(a, rm, (os + rm.m.Values + rm.ns));
print "istEinKlon = ", result;

print "\n\n";

print "\nDone\n";
}
// end








method {:verify false} Main2() {

print "main showing RefOK etc\n";

var t := new Object.make(protoTypes, {}, {}, "t");

//   t
//   a       b       c
//   d  e            f
//  ij kl            g
//                   h

var a := new Object.make(protoTypes, {t}, {t},         "a");
var b := new Object.make(protoTypes, {t}, {t},         "b");
var c := new Object.make(protoTypes, {t}, {t},         "c");
var d := new Object.make(protoTypes, {a}, {a,t},       "d");
var e := new Object.make(protoTypes, {a}, {a,t},       "e");
var f := new Object.make(protoTypes, {c}, {t,a,c},     "f");
var g := new Object.make(protoTypes, {f}, {t,a,c,f},   "g");
var h := new Object.make(protoTypes, {g}, {t,a,c,f,g}, "h");
var i := new Object.make(protoTypes, {c}, {t,a,d},     "i");
var j := new Object.make(protoTypes, {c}, {t,a,d},     "j");
var k := new Object.make(protoTypes, {c}, {t,a,e},     "k");
var l := new Object.make(protoTypes, {c}, {t,a,e},     "l");


var os : set<Object> := {t,   a, b, c, d, e, f, g, h, i, j, k, l };
var oq : seq<Object> := [t,   a, b, c, d, e, f, g, h, i, j, k, l ];

assert forall o <- oq :: o.Ready();

//   for i := 0 to |oq|
//     {
//       var o : Object := oq[i];
//
//       assert o.Ready();
//
//       print "\n=============================================================\n";
//       print "=============================================================\n";
//
//       printobject(o);
//     }
//    print "\n\n";


print "\n\nOwnership - Inside =========================\n";
print "Ownership - Inside =========================\n\n";

//       for i := 0 to |oq|
//        {
//          printobj(oq[i]);
//          print "  ";
//
//          for j := 0 to |oq|
// {
//          print (if (inside(oq[i],oq[j])) then "i" else " ");
//          print " ";
// }
//          print "\n";
//
//        }
//   print "\n\n";

      for i := 0 to |oq|
       {
        print oq[i].nick;
//         printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then (oq[i].nick+"<="+oq[j].nick) else "    ");
         print " ";
}
         print "\n";

       }
  print "\n\n";
  print "\n[\n";

      for i := 0 to |oq|
       {
         print "\"";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then ("x") else " ");
}
         if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}

       }
print "]\n";





var matrix : seq<string>:= [
"x            ",
"xx           ",
"x x          ",
"x  x         ",
"xx  x        ",
"xx   x       ",
"x  x  x      ",
"x  x  xx     ",
"x  x  xxx    ",
"x  x     x   ",
"x  x      x  ",
"x  x       x ",
"x  x        x"
];

  print "\n\n";

      for i := 0 to |matrix|
       {
         for j := 0 to |matrix[0]|
          {
         print match (inside(oq[i],oq[j]), (matrix[i][j]) )
           case (true,  'x') => "o"  //OK, true positive
           case (true,  ' ') => "F"  //false positive
           case (false, ' ') => " "  //OK, true negative
           case (false, 'x') => "M"; //false negative
          }
         print "\n";
       }
print "\n";



print "ownerInsideOwner ownerInsideOwner ownerInsideOwner ownerInsideOwner\n";
print "ownerInsideOwner ownerInsideOwner ownerInsideOwner ownerInsideOwner\n";

      for i := 0 to |matrix|
       {
         for j := 0 to |matrix[0]|
          {
         print match (ownerInsideOwner(oq[i].AMFO,oq[j].AMFO), (matrix[i][j]) )
           case (true,  'x') => "o"  //OK
           case (true,  ' ') => "M"  //missing
           case (false, ' ') => " "
           case (false, 'x') => "F"; //false posiutive, ie FUCKED
          }
         print "\n";
       }
print "\n";


print "FUCKED FUCKED FUCKED FUCKED FUCKED\n";
print "FUCKED FUCKED FUCKED FUCKED FUCKED\n";

print "\n\nREFERENCE OK refOK =========================\n";
print "REFERENCE OK refOK =========================\n\n";

      for i := 0 to |oq|
       {
         print oq[i].nick;
         //printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then (oq[i].nick+"->"+oq[j].nick) else "    ");
         print " ";
}
print "\n";
}

//uncomment to print out a new "matrix"
//
//
//   print "\n[\n";
//
//       for i := 0 to |oq|
//        {
//          print "\"";
//
//          for j := 0 to |oq|
// {
//          print (if (refOK(oq[i],oq[j])) then ("x") else " ");
// }
//          if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}
//
//        }
// print "]\n";


var keanu :=
[
"xxxx         ",
"xxxxxx       ",
"xxxx         ",
"xxxx  x  xxxx",
"xxxxxx       ",
"xxxxxx       ",
"xxxx  xx xxxx",
"xxxx  xxxxxxx",
"xxxx  xxxxxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx"
];


  print "\n\n";

      for i := 0 to |keanu|
       {
         for j := 0 to |keanu[0]|
          {
         print match (refOK(oq[i],oq[j]), (keanu[i][j]) )
           case (true,  'x') => "o"  //OK, true positive
           case (true,  ' ') => "F"  //false positive
           case (false, ' ') => " "  //OK, true negative
           case (false, 'x') => "M"; //false negative
          }
         print "\n";
       }
print "\n";


print "\nDone\n\n";





}

// end main2




method {:verify false} Main3() {

print "main poking at bound etc\n";
print "Object G has bound at object t\n";

var t := new Object.make(protoTypes, {}, {}, "t");

//   t
//   a       b       c
//   d  e            f
//  ij kl            g
//                   h

var a := new Object.make(protoTypes, {t}, {t},         "a");
var b := new Object.make(protoTypes, {t}, {t},         "b");
var c := new Object.make(protoTypes, {t}, {t},         "c");
var d := new Object.make(protoTypes, {a}, {a,t},       "d");
var e := new Object.make(protoTypes, {a}, {a,t},       "e");
var f := new Object.make(protoTypes, {c}, {t,a,c},     "f");
var g := new Object.make(protoTypes, {f}, {t,a,c,f},   "G", {t});
var h := new Object.make(protoTypes, {g}, {t,a,c,f,g}, "H", {g});
var i := new Object.make(protoTypes, {d}, {t,a,d},     "i");
var j := new Object.make(protoTypes, {d}, {t,a,d},     "j");
var k := new Object.make(protoTypes, {e}, {t,a,e},     "k");
var l := new Object.make(protoTypes, {e}, {t,a,e},     "l");

print "a->d : ", refOK(a,d), "\n";
print "a->e : ", refOK(a,e), "\n";

var os : set<Object> := {t,   a, b, c, d, e, f, g, h, i, j, k, l };
var oq : seq<Object> := [t,   a, b, c, d, e, f, g, h, i, j, k, l ];

assert forall o <- oq :: o.Ready();

print "\n\nREFERENCE OK refOK =========================\n";
print "REFERENCE OK refOK =========================\n\n";

      for i := 0 to |oq|
       {
         print oq[i].nick;
         //printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then (oq[i].nick+"->"+oq[j].nick) else "    ");
         print " ";
}
print "\n";
}




  print "\n[\n";

      for i := 0 to |oq|
       {
         print "\"";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then ("x") else " ");
}
         if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}

       }
print "]\n";


var keanu :=
[
"xxxx         ",
"xxxxxx       ",
"xxxx         ",
"xxxx  x  xxxx",
"xxxxxx       ",
"xxxxxx       ",
"xxxx  xx xxxx",
"xxxx  xxxxxxx",
"xxxx  xxxxxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx"
];


  print "\n\n";

      for i := 0 to |keanu|
       {
         for j := 0 to |keanu[0]|
          {
         print match (refOK(oq[i],oq[j]), (keanu[i][j]) )
           case (true,  'x') => "o"  //OK, true positive
           case (true,  ' ') => "F"  //false positive
           case (false, ' ') => " "  //OK, true negative
           case (false, 'x') => "M"; //false negative
          }
         print "\n";
       }
print "\n";


print "\nDone\n\n";





} //end Main3


method {:verify false} Main4() {

print "long and thin study of bounds\n";

var t := new Object.make(protoTypes, {}, {}, "t");  //top;

print "   t\n";

var depth  : nat := 5;
var prev   := t;
var os := {t};
var oq := [t];

var o2 : Object? := null;

for i := 0 to depth
{
  var spine := new Object.make(protoTypes, {prev}, os, "o"+natToString(i));

  if (i == 1)  {o2 := prev;}

  var pbound := {prev};
  if (i == 2) {pbound := {};}
  if (i == 3) {pbound := {o2};}

  var peer  := new Object.make(protoTypes, {prev}, os, "p"+natToString(i), pbound);
  prev := spine;

  os := os + {spine, peer};
  oq := oq + [spine, peer];
}

print "Ownership - Directly Inside =========================\n\n";

      for i := 0 to |oq|
       {
        print oq[i].nick;
//         printobj(oq[i]);
         print " owns ";

         for j := 0 to |oq|
{
         print (if (directlyInside(oq[j],oq[i])) then (oq[j].nick+" ") else "");
}
         print "\n";

       }
  print "\n\n";


print "Owners & Bound =========================\n\n";

      for i := 0 to |oq|
       {
        print oq[i].nick;
//         printobj(oq[i]);

         print " owner=";
         for j := 0 to |oq|
         {
         print (if (directlyInside(oq[i],oq[j])) then (oq[j].nick+" ") else "");
         }

         print " bound=";
         for j := 0 to |oq|
         {
         print (if (directlyBounded(oq[i],oq[j])) then (oq[j].nick+" ") else "");
         }

         print "\n";

       }
  print "\n\n";




//
//
// print "Ownership - Directly Inside =========================\n\n";
//
//       for i := 0 to |oq|
//        {
//         print oq[i].nick;
// //         printobj(oq[i]);
//          print "  ";
//
//          for j := 0 to |oq|
// {
//          print (if (directlyInside(oq[i],oq[j])) then (oq[i].nick+"<<"+oq[j].nick) else "      ");
//          print " ";
// }
//          print "\n";
//
//        }
//   print "\n\n";


print "Ownership - Inside =========================\n\n";

//       for i := 0 to |oq|
//        {
//          printobj(oq[i]);
//          print "  ";
//
//          for j := 0 to |oq|
// {
//          print (if (inside(oq[i],oq[j])) then "i" else " ");
//          print " ";
// }
//          print "\n";
//
//        }
//   print "\n\n";

      for i := 0 to |oq|
       {
        print oq[i].nick;
//         printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then (oq[i].nick+"<="+oq[j].nick) else "      ");
         print " ";
}
         print "\n";

       }
  print "\n\n";



print "\n\nREFERENCE OK refOK =========================\n";
print "REFERENCE OK refOK =========================\n\n";

      for i := 0 to |oq|
       {
         print oq[i].nick;
         //printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then (oq[i].nick+"->"+oq[j].nick) else "    ");
         print " ";
}
print "\n";
}




  print "\n[\n";

      for i := 0 to |oq|
       {
         print "\"";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then ("x") else " ");
}
         if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}

       }
print "]\n";


} //end Main4
