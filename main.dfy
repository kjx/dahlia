



//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/// Main, TESTS  etc
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


const protoTypes : map<string, Mode> := map["jat":= Evil]["dat":=Evil]
         ["cat":= Evil]["rat":= Evil]["nxt":= Evil]
         ["eye":= Evil]["kye":= Evil]["lat":= Evil]
         ["fucker" := Evil]








method {:verify false} DMain()  {
  
var t := new Object.frozen(protoTypes);
t.nick := "t";


// assert t.Ready();

var a := new Object.make(protoTypes, t, {t}, "a");

// assert a.Ready();

 
var b := new Object.make(protoTypes, t, {t}, "b");
var c := new Object.make(protoTypes, t, {t}, "c");

// assert c.TRUMP();

var d := new Object.make(protoTypes, a, {t,a}, "d");

// label here:
// assert DTRUMP: d.TRUMP(); 

var e := new Object.make(protoTypes, a, {t,a}, "e");

// assert c.Ready();
// assert c.TRUMP() by { //////reveal c.TRUMP();
//  }
// //  assert c.MOGO();
//   assert c.Ready();
//   assert c.Valid();

// assert c.TRUMP() by { //////reveal c.TRUMP();
//  }

var f := new Object.make(protoTypes, c, {t,a,c},     "f");
var g := new Object.make(protoTypes, f, {t,a,c,f},   "g");
var h := new Object.make(protoTypes, g, {t,a,c,f,g}, "h");

//assert d.Valid();

// assert d.TRUMP() by { assert unchanged@here(d);
//      //////reveal d.TRUMP(), DTRUMP; 
//      }
  

}//end DMain()
















method {:verify false} Main() {

  print "Hello\n";
  
var t := new Object.frozen(protoTypes);
t.nick := "t";

//   t
//   a       b       c
//   d  e            f 
//  ij kl            g 
//                   h

assert t.Ready();

var a := new Object.make(protoTypes, t, {t}, "a");
assert AYY: AOK(a, {t,a});

var b := new Object.make(protoTypes, t, {t}, "b");
var c := new Object.make(protoTypes, t, {t}, "c");

assert CEE: AOK(c, {t,c});

var d := new Object.make(protoTypes, a, {a,t}, "d");

var e := new Object.make(protoTypes, a, {a,t}, "e");

var f := new Object.make(protoTypes, c, {t,a,c},     "f");

var g := new Object.make(protoTypes, f, {t,a,c,f},   "g");

var h := new Object.make(protoTypes, g, {t,a,c,f,g}, "h");

assert AOK(c, {t,c})  by { reveal CEE; }

var i := new Object.make(protoTypes, c, {t,a,d},     "i");
var j := new Object.make(protoTypes, c, {t,a,d},     "j");
var k := new Object.make(protoTypes, c, {t,a,e},     "k");
var l := new Object.make(protoTypes, c, {t,a,e},     "l");


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

var os : set<Object> := {t,   a, b, c, d, e, f, g, h, i, j, k, l};

//b.fields := b.fields["fucker" := h];
// // b.fieldModes := b.fieldModes["fucker" := Rep];

AOKWiderContext(i, {t,a,d,i},  os);

i.fields := map["jat":= j]["dat":=d]["cat":= c]["rat":= a];

assert i.AllFieldsAreDeclared();
assert i.AllFieldsContentsConsistentWithTheirDeclaration();
assert i.AllOutgoingReferencesAreOwnership(os);
assert i.AllOutgoingReferencesWithinThisHeap(os);
assert AOK(i,os);

j.fields := map["nxt":= i];

k.fields := map["lat":= l]["dat":=d]["cat":= c]["rat":= a];
l.fields := map["nxt":= k];

d.fields := map["eye":=i];
e.fields := map["kye":=k];

assert AllOK(os, os);

print "done setup\n";

var isomap := map[d:=e,i:=k,j:=l,t:=t,a:=a,b:=b,c:=c];

var iddmap := map[d:=d,i:=i,j:=j,t:=t,a:=a,b:=b,c:=c];


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

//print "walkiesClean CLEAN CLEAN CLEAN\n";
//var tb, tm, ts := walkiesClean(d,d,map[],os,os);

var m' := Map(map[], {}, {}, i, os, {} );

var tb, tmm := Clone_Via_Map(i, m');

var tm := tmm.m;
var ts := tmm.oHeap;

// 
//     m : Mapping,  //m : Mapping 
//     ks : set<Object>, //ks - set, keys of the mapping   (must be m.Keys, subset of oHeap)
//     vs : set<Object>, //vs - set, values or the mapping (must be m.Values, subset of oHeap + ns)
//     o : Object,  //o - Owner within which the clone is being performaed, in oHeap
//     oHeap : set<Object>,  //oHeap - original (sub)heap contianing the object being cloned and all owners and parts 
//     ns : set<Object>) 

print "+++++++++++++\n";
print "original store (os)\n";
print "+++++++++++++\n";
printobjectset(os);
print "+++++++++++++\n";
print "clones tm.Values - os\n";
print "+++++++++++++\n";
printobjectset(tm.Values - os);
print "+++++++++++++\n";
printmapping(tm);

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

var ok, kos :=  walkiesIsoOK(i, tb, i, tm, os);

print "walkes is ",ok,"\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

return; 

var dv, dos := walkiesIsoOK(d, e,  d, isomap, os);
print "%%%%% d to d ", dv, "\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

var ev, eos := walkiesIsoOK(d, d, d, iddmap, os);
print "%%%%% d to e ", ev, "\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

var av, aos := walkiesIsoOK(a, b, a, map[], os);
print "%%%%% a to b (nomap)", av, "\n";

av, aos := walkiesIsoOK(a, b, a, map[a:=b], os);
print "%%%%% a to b (partialmap)", av, "\n";

av, aos := walkiesIsoOK(a, b, a, map[a:=b,t:=t], os);
print "%%%%% a to b (fullmap)", av, "\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

var bv, bos := walkiesIsoOK(b, f, a, map[], os);
print "%%%%% b to f (nomap) ", bv, "\n";

bv, bos := walkiesIsoOK(b, f, a, map[b:=f,t:=c], os);
print "%%%%% b to f (map) ", bv, "\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

return;

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";
print "d to e ", isIsomorphicMappingOWNED(d, d, isomap, os), "\n";
printmappingIsIsomorphic(isomap,d,os);
print "\n";
print "j to l ", isIsomorphicMappingOWNED(j, d, isomap, os), "\n";

printobject(i);
printobject(j);
printobject(k);
printobject(l);

print "\n////////////////////////////////////////////////////////////\nOBJECT d\n";
print "d to d ", isIsomorphicMappingOWNED(d, d, iddmap, os), "\n";


///////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////

print "\n////////////////////////////////////////////////////////////\nOBJECT d\n";
printobject(d);
print "OBJECT d.eye\n";
printobject(d.fields["eye"]);
print "////////////////////////////////////////////////////////////\nCLONE d -> dd\n";
var dd, mapdd, dddds := walkiesClean(d, d, map[], os, os); 
mapdd:= mapdd[t:=t];
printobject(dd);
print "\n////////////////////////////////////////////////////////////\nOBJECT dd\n";

//KJX - should track thisthrough5 the clone!!!
if ("eye" in dd.fields)  
    { printobject(dd.fields["eye"]); }
  else { print "FUCK FUCK eye missin\n"; }

print "////////////////////////////////////////////////////////////\nMAPPING d -> dd\n";
print isIsomorphicMappingOWNED(d, d, mapdd, os + mapdd.Values), "\n";
printmappingIsIsomorphic(mapdd, d, os + mapdd.Values);
printIsomorphicOWNED(d, d, mapdd, os + mapdd.Values);
print "////////////////////////////////////////////////////////////\n";
print "////////////////////////////////////////////////////////////\n";
print "////////////////////////////////////////////////////////////\n\n";
// printobject(dd);
// print "\n";
// printmapping(mapdd);
// print "\n\n";
// printobject(i);

// print "\n";
return;
print "\n////////////////////////////////////////////////////////////\nOBJECT i\n";
printobject(i);
print "////////////////////////////////////////////////////////////\nOBJECT ii\n";
var ii, mapii, iiiis := walkiesClean(i, i, map[], os, os);
printobject(ii);
print "////////////////////////////////////////////////////////////\nMAPPING i -> ii\n";
print isIsomorphicMappingOWNED(i, i, mapii, os + mapii.Values), "\n";
printmapping(mapii);
printIsomorphicOWNED(i, i, mapii, os + mapii.Values);
print "////////////////////////////////////////////////////////////\n";
print "////////////////////////////////////////////////////////////\n";
print "////////////////////////////////////////////////////////////\n\n";
// printobject(ii);
// print "\n";
// printmapping(mapii);

return;

print "about to ISO\n";

print "ISOMORPH2:tt:", isIsomorphicMappingOWNED(t, t, map[ d:= d,a:=a,t:=t], os),"\n";
print "ISOMORPH2:aa:", isIsomorphicMappingOWNED(a, a, map[ d:= d,a:=a,t:=t], os),"\n";

print "ISOMORPH1:de:", isIsomorphicMappingOWNED(d, d, map[ d:= e], os),"\n";
print "ISOMORPH2:dd:", isIsomorphicMappingOWNED(d, d, map[ d:= d], os),"\n";

print "ISOMORPH1:de:", isIsomorphicMappingOWNED(d, d, map[ d:= e,a:=a,t:=t], os),"\n";
print "ISOMORPH2:dd:", isIsomorphicMappingOWNED(d, d, map[ d:= d,a:=a,t:=t], os),"\n";

print "t, t\n";
printIsomorphicOWNED(t, t, map[ d:= e,a:=a,t:=t], os);

print "a, a\n";
printIsomorphicOWNED(a, a, map[ d:= e,a:=a,t:=t], os);


print "d, e\n";
printIsomorphicOWNED(d, d, map[ d:= e,a:=a,t:=t], os);
print "e, e\n";
printIsomorphicOWNED(d, d, map[ d:= d,a:=a,t:=t], os);

print "d, e\n";
printIsomorphicOWNED(d, d, map[ d:= e], os);
print "e, e\n";
printIsomorphicOWNED(d, d, map[ d:= d], os);

var oq : seq<Object> := [t,   a, b, c, d, e, f, g, h, i, j, k, l ];

assert forall o <- oq :: o.Ready();

  for i := 0 to |oq|
    {
      var o : Object := oq[i];

      assert o.Ready();

      print "\n=============================================================\n";
      print "=============================================================\n";

      printobject(o);
    }
   print "\n\n";

      for i := 0 to |oq|
       {
         printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then "i" else " ");
         print " ";
}
         print "\n";

       } 
  print "\n\n";

      for i := 0 to |oq|
       {
         printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then (oq[i].nick+oq[j].nick) else "  ");
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
"x        ",
"xx       ",
"x x      ",
"x  x     ", 
"xx  x    ",
"xx   x   ",
"x  x  x  ",
"x  x  xx ",
"x  x  xxx"
];

  print "\n\n";

      for i := 0 to |matrix|
       {
         for j := 0 to |matrix[0]|
          {
         print match (inside(oq[i],oq[j]), (matrix[i][j]) )
           case (true,  'x') => "x"
           case (true,  ' ') => "M"  //missing
           case (false, ' ') => " "
           case (false, 'x') => "F"; //false posiutive, ie FUCKED
          }
         print "\n";
       }
print "\n";


print "\nDone\n\n";

var inverted := partitionedIncomingEdges(edges(os));

print inverted, "\n";

printedgemap(inverted);

print "\n\nHxR\n";

var hxr := HxR(edges(os));

print hxr,"\n\n"; 

print "\nDone\n";
} 
// end main






//////////////////////////////////////////////////////////////////////////////
// "test" lemmas etc

lemma {:timeLimit 10}  ownersFuckingowners5(a : Object, b : Object, os : set<Object>) 
  requires a.Ready()
  requires b.Ready()
  // requires OutgoingReferencesAreInTheseObjects(os)
  // requires StandaloneObjectsAreValid(os)
  requires a in os
  requires b in os
  requires a.region.Heap?
{  
  assert inside(a,b) == (b in owners(a)) || b == a;
}

lemma ownersFuckingowners6(b : Object) 
  decreases b.AMFO
  requires b.Ready()
{  assert b.OwnersValid();
  if (b.region.World?) {
    assert b.AMFO == {};
    assert owners(b)== {};
    return;
  }
  assert (b.region.Heap?);
  if (b.region.Heap?) {
    assert b.AMFO == b.region.owner.AMFO + {b.region.owner};
    assert owners(b)== owners(b.region.owner) + {b.region.owner};
    ownersFuckingowners6(b.region.owner);
    return;
  }
}


lemma ICanPointToWhatMyOwnerCanPointTo(o : Object, oo : Object, t : Object)
  requires o.Ready()
  requires oo.Ready()
  requires o.region.Heap?
  requires o.region.owner == oo
  requires refOK(oo,t)
  ensures  refOK(o,t)
{ //////reveal Object.Ready();
 } 
         
 
lemma e2x(os : set<Object>, es : set<Edge>) 
   //reads (set o <- os, o2 <- o.ValidReadSet() :: o2)
   requires forall e <- es :: e.t in os
   requires forall o <- os :: o.Ready() && o.Valid()
   requires es == edges(os)
   ensures OutgoingReferencesAreInTheseObjects(os)
{

  assert forall e <- es :: e.t in os;

  crud_3(os,es); crud_2(os,es); crud_1(os,es); crud1(os,es); crud2(os,es); crud3(os,es);

  // assert forall e <- (set o <- os, n <- o.fields :: Edge(o, n, o.fields[n])) :: e.t in os;
  // assert (forall o <- os, n <- o.fields :: Edge(o, n, o.fields[n]).t in os);
  // assert (forall o <- os, n <- o.fields :: o.fields[n] in os);
  // assert (forall o <- os :: o.fields.Values <= os);
  // assert (forall o <- os :: o.outgoing() <= os);
  assert OutgoingReferencesAreInTheseObjects(os);
}


lemma crud_3(os : set<Object>, es : set<Edge>) 
    requires forall o <- os :: o.Ready() && o.Valid()
    requires forall e <- edges(os) :: e.t in os
    ensures forall e <- (set o <- os, n <- o.fields :: Edge(o, n, o.fieldModes[n], o.fields[n])) :: e.t in os
   {
   }

lemma crud_2(os : set<Object>, es : set<Edge>) 
    requires forall o <- os :: o.Ready() && o.Valid()
    requires forall e <- (set o <- os, n <- o.fields :: Edge(o, n, o.fieldModes[n], o.fields[n])) :: e.t in os
    ensures  (forall o <- os, n <- o.fields :: Edge(o, n, o.fieldModes[n], o.fields[n]).t in os)
   {
   }


lemma crud_1(os : set<Object>, es : set<Edge>) 
    requires forall o <- os :: o.Ready() && o.Valid()
    requires (forall o <- os, n <- o.fields :: Edge(o, n, o.fieldModes[n], o.fields[n]).t in os)
    ensures  (forall o <- os, n <- o.fields :: o.fields[n] in os)
   {
   }

lemma crud1(os : set<Object>, es : set<Edge>) 
    requires  (forall o <- os, n <- o.fields :: o.fields[n] in os)
   ensures  (forall o <- os :: o.fields.Values <= os)
   {
   }

lemma crud2(os : set<Object>, es : set<Edge>) 
    requires   (forall o <- os :: o.fields.Values <= os)
    ensures (forall o <- os :: o.outgoing() <= os)
   {
   }

lemma crud3(os : set<Object>, es : set<Edge>) 
    requires (forall o <- os :: o.outgoing() <= os)
    ensures OutgoingReferencesAreInTheseObjects(os)
   {
   }















  