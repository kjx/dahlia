
const protoTypes : map<string, Mode> := map["jat":= Evil]["dat":=Evil]
         ["cat":= Evil]
         ["rat":= Evil]
         ["nxt":= Evil]
         ["eye":= Evil]
         ["kye":= Evil]
         ["lat":= Evil]
         ["fucker" := Evil]




method {:verify false} Main() {

  print "Main Test for loopback\n";
  
var t := new Object.frozen(protoTypes);
t.nick := "t";

//   t
//   a      b c 
//   d
//   e f g h 

assert t.Ready();
assert COK(t, {t});

// protoTypes 8-)
// cat dat eye fucker jat kye lat nxt rat 

var a := new Object.cake(protoTypes, t, {t}, "a");

var b := new Object.cake(protoTypes, t, {t}, "b");

var c := new Object.cake(protoTypes, t, {t}, "c");

var d := new Object.cake(protoTypes, a, {t,a}, "d");  

var e := new Object.cake(protoTypes, d, {t,a,d}, "e"); //we're gonna clone this one..?

var f := new Object.cake(protoTypes, e, {t,a,d,e}, "f");

var g := new Object.cake(protoTypes, f,  {t,a,d,e,f},   "g");

var h := new Object.cake(protoTypes, g, {t,a,d,e,f,g}, "h");


var i := new Object.cake(protoTypes, e, {t,a,d,e,f,g,h}, "i");
var j := new Object.cake(protoTypes, e, {t,a,d,e,f,g,h}, "j");
var k := new Object.cake(protoTypes, e, {t,a,d,e,f,g,h}, "k");
var l := new Object.cake(protoTypes, e, {t,a,d,e,f,g,h}, "l");


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

a.fields := map["eye":=d];
d.fields := map["lat":= e]["dat":=f]["cat":=g]["rat":= h];

assert COK(a,os);

assert d.AllFieldsAreDeclared();
assert d.AllFieldsContentsConsistentWithTheirDeclaration();
assert d.AllOutgoingReferencesAreOwnership(os);
assert d.AllOutgoingReferencesWithinThisHeap(os);
assert COK(d,os);


assert CallOK(os);

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

print "about to clone a\n";

var m := Map(map[], {}, {}, a, os, {} );

var ra, rm := Clone_Via_Map(a, m);

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
printobjectset(rm.m.Values - os);
print "+++++++++++++\n";
printmapping(rm.m);


print "\nDone\n";
} 
// end




