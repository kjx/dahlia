


method printobject(o : Object)
{
      printobj(o);
      print "\n  ";
      printset(o.allExternalOwners());
      print "\n";
      printobjfields(o);
}

method printset(s : set<Object>)
{
  var t := s;
  while t != {}
    decreases t
  {
    var y: Object;
    y :| y in t;
    printobj(y);
    print " ";
    t := t - {y};
  }
}


method printobjectset(s : set<Object>)
{
  var t := s;
  while t != {}
    decreases t
  {
    var y: Object;
    y :| y in t;
    printobject(y);
    print "- - - - - - - -\n";
    t := t - {y};
  }
}


method printedgeset(s : set<Edge>)
{
  var t := s;
  while t != {}
    decreases t
  {
    var y: Edge;
    y :| y in t;
    print y, "  ";
    t := t - {y};
  }
}


method printedgemap(m : Incoming)
{
  var t := m;
  while t != map[]
    decreases t
  {
    var y: Object;
    y :| y in t.Keys;
    printobj(y);
    print (|t[y]|);
    print ":= ";
    printedgeset(t[y]);
    t := t - {y};
    print "\n";
  }
}


function fmtobj(o : Object) : string
   reads o
{
  "Obj(" + o.nick + ")"
}

method printobj(o : Object)
  ensures unchanged(o)
  modifies {}
{
 print "Obj(", o.nick, ")";
}


function fmtown(oo : Owner) : string
   reads oo
{
  "Own(" + fmtnickset(oo) + ")"
}

method printown(oo : Owner)
  ensures unchanged(oo)
  modifies {}
{
 print fmtown(oo);
}


//should alos print field modes?
method printobjfields(o : Object)
{
  var t := o.fields;
  while t != map[]
    decreases t
  {
    var y: string;
    y :| y in t.Keys;
    print " ";
    print y,":=";
    printobj(t[y]);
    t := t - {y};
    print "\n";
  }
}

method printmapping(m: vmap<Object,Object>)
  modifies {}
  ensures unchanged(m.Keys,m.Values)
{
  var t := m;
  while t != map[]
    decreases t
  {
    var y: Object;
    y :| y in t.Keys;
    print " ";
    printobj(y);
    print ":=";
    printobj(t[y]);
    t := t - {y};
    print "\n";
  }
}



method printmappingIsIsomorphic(m: vmap<Object,Object>, o : Object, os : set<Object>)
{
  var t := m;
  while t != map[]
    decreases t
  {
    var y: Object;
    y :| y in t.Keys;
    print " ";
    printobj(y);
    print ":=";
    printobj(t[y]);
    print "  ";
//    print isIsomorphicMappingOWNED(y, o, m, os);
    print "\n";
    t := t - {y};
   }
}






//iterative clone-checker, most likely only dynamic at this point
method istEinKlon(src : Object, m : Klon, context : set<Object>) returns (rv : bool)
  requires src in m.m.Keys
  requires src in context
  requires m.m.Keys   <= context
  requires m.m.Values <= context
{
  rv := true;
  var os := context;
  while os != {}
    decreases os
    invariant os <= context
  {
    var o: Object;
    o :| o in os;
    os := os - {o};

    if (outside(o,src)) { print "   skipping "+fmtobj(o)+" outside src\n"; continue; }
    if (o !in m.m.Keys) { print "   skipping "+fmtobj(o)+" outside Klon \n"; continue; }

    var k := m.m[o];  //k klon of o

    print "   checking ",fmtobj(o)," cloned as ",fmtobj(k), " ";

    rv :=
         && istKlonnyKlon(o.bound, k.bound, m)
         && istKlonnyKlon(o.owner, k.owner, m)
         && istKlonAlleFelder(o, k, m)
         ;

   print rv,"\n";
  }
}

predicate istKlonnyKlon(os : set<Object>, ks : set<Object>, m : Klon)
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
  decreases os, 50

{
  && (forall o <- os :: o in m.m.Keys)
  && (mapThruKlon(os, m) == ks)
}

predicate istKlonAlleFelder(o : Object, k : Object, m : Klon)
  reads o`fields, o`fieldModes
  reads k`fields, k`fieldModes
{
  && (o.fields.Keys     == k.fields.Keys)
  && (o.fieldModes.Keys == k.fieldModes.Keys)
  && (o.fields.Values     <= m.m.Keys)
  && (forall f <- o.fields.Keys :: (m.m[o.fields[f]]  == k.fields[f]))
//  && ()   //at some point needs to check mapping for fieldModes?
}



// method printIsomorphicOWNED(a : Object, o : Object, m : vmap<Object,Object>, os : set<Object>)
//   decreases os

//   {
//    print "(a in m) ", (a in m), "\n";
//    if (a !in m) { return; }
//    var b := m[a];
//    print "a == b ", a == b, "\n";
//    if (a == b) { return; }
//    print "({a,b} <= os) ",({a,b} <= os),"\n";
//    //print "(m[a] == b) ", (m[a] == b), "\n";

//    print "(recurse on owner) ", isIsomorphicMappingOWNED(a.owner, o, m, os - {a,b}),"\n";

//   print "Owners overall ",
//     isIsomorphicMappingOWNED(a.owner, o, m, os - {a,b}) ,"\n";

//   print "Field names ", (a.fields.Keys == b.fields.Keys), "\n";

//   if (a.fields.Keys != b.fields.Keys) {
//       print "oops! a: ", a.fields.Keys,"\n";
//       print "oops! b: ", b.fields.Keys,"\n";
//       return; }

//   var ns : seq<string> := set2seq(a.fields.Keys);

//   for i := 0 to |ns|
//    {
//     var n : string := ns[i];
//     print "  ";
//     print "a.",n," :=";
//     printobj(a.fields[n]);
//     print " - ";
//     print "b.",n," :=";
//     printobj(b.fields[n]);
//     print "\n";

//     print "   a.",n," in m ", a.fields[n] in m, "\n";
//     if (a.fields[n] !in m) {return;}
//     print "   ",n," in b.fields ", n in b.fields, "\n";
//     if (n !in b.fields) {return;}
//     print "   b.fields[",n,"] == m[a.fields[",n,"]] ",(b.fields[n] == m[a.fields[n]]) , "\n";
// //    print " (recurse on field ",n,") ", isIsomorphicMappingOWNED(a.fields[n], o, m, os - {a,b}),"\n";
//    }
// }



function fmtnickset(Y: set<Object>) : string
 reads Y`nick
 {
   fmtsetstr( set y <- Y :: y.nick )
 }

method mlurk(x: set<string>) returns (r: string)
 requires |x| > 0
 {
  r :| r in x;
 }


lemma {:axiom} StrLEQ1(a : string,  b : string)
  ensures (strLEQ(a, b) && strLEQ(b, a)) <==> (a == b)

lemma {:axiom}  StrLEQ2(a : string,  b : string, c : string)
  ensures (strLEQ(a, b) && strLEQ(b, c)) ==> strLEQ(a, c)

lemma {:axiom} StrLEQ3(a : string,  b : string)
  ensures  strLEQ(a, b) || strLEQ(b, a)

lemma {:axiom} StrLEQ4(a : string)
  ensures  strLEQ(a, a)



ghost function anyOneOf(s: set<string>) : string
  requires |s| > 0
{
  ExtractFromNonEmptySet(s)
 }


predicate IAMTheRessurection(s: set<string>, m : string)
{
  m in s && forall x <- s :: strLEQ(m, x)
}

predicate OnlyRessurection(s: set<string>, m : string)
  requires m in s
  requires IAMTheRessurection(s,m)
  {
   forall x <- s | IAMTheRessurection(s,x) :: x == m
  }

lemma ReallyJustOneRessurection(s: set<string>,  m : string, mm : set<string>)
  requires m in s
  requires IAMTheRessurection(s,m)
  requires mm == set x <- s | IAMTheRessurection(s,x) :: x
  //ensures |mm| == 1
  ensures mm == {m}
  {
    OneRessurection(s,m);
  }

lemma OneRessurection(s: set<string>, m : string)
  requires m in s
  requires IAMTheRessurection(s,m)
  ensures  forall x <- s | IAMTheRessurection(s,x) :: x == m
{
  assert m in s;
  forall x <- s | IAMTheRessurection(s,x)
    ensures  x == m //by
      {
         if (x == m) {
           assert IAMTheRessurection(s,m);
           assert strLEQ(x,m);
           assert strLEQ(m,x);
           assert IAMTheRessurection(s,x);
           assert x == m;
         } else {
            assert {:contradiction} IAMTheRessurection(s,m);
            assert {:contradiction} x in s;
            assert {:contradiction} strLEQ(m,x);
            assert {:contradiction} IAMTheRessurection(s,x);
            assert {:contradiction} m in s;
            assert {:contradiction} strLEQ(x,m);
            StrLEQLEQIsEQ(x,m);
            assert {:contradiction} x == m;
            assert {:contradiction} false;
         }
      }
}

lemma LemmaSTREQ(x : string, y : string)
 ensures (x == y) ==> strLEQ(x,y)
 ensures (x == y) ==> strLEQ(y,x)
{}

lemma MemmaSTREQ(s : set<string>)
    requires |s| == 1
  ensures exists m <- s :: m in s
  ensures exists m <- s :: forall x <- s :: strLEQ(m, x)
   {
     //var v : string :| v in s;
     var v := ExtractFromSingleton(s);
     assert s == {v};
     forall x <- s ensures x == v  {
      if (x == v) {
          LemmaSTREQ(x,v);
          assert strLEQ(x,v) && strLEQ(v,x);
          assert forall x <- {v} :: strLEQ(v, x);
          assert forall x <- s :: strLEQ(v, x);
          assert exists m <- s :: forall x <- s :: strLEQ(m, x);
          return; }
      assert x != v;
      LemmaSingletonEquality(s, x, v);
      assert {:contradition} x == v;
      assert {:contradition} false;
     }
     assert forall x <- s :: x == v;

    forall x <- s ensures strLEQ(x,v) {
        assert x == v;
        LemmaSTREQ(x,v);
        assert  strLEQ(x,v);
    }
   }


lemma MummaSTREQ(s : set<string>)
//unfinished - wasted LOTS of time on this now
    decreases s
    requires |s| > 0
    // ensures  exists m <- s :: m in s
    // ensures  exists m <- s :: forall x <- s :: strLEQ(m, x)
   {
     if (|s| == 1) { MemmaSTREQ(s); return; }
     assert |s| > 1;
     var v : string :| v in s;
     var t := s - {v};
     MummaSTREQ(t);
//     assert exists m <- t :: forall x <- s :: strLEQ(m, x);

//     var q  : string :| q in s && forall x <- s :: strLEQ(q, x);



   }




lemma EveryPlanetHasANorth(s : set<string>)
  requires |s| > 0
  // ensures  exists m <- s :: forall x <- s :: strLEQ(m, x)
  // ensures  forall m <- s, n <- s ::
  //     (&& (forall x <- s :: strLEQ(m, x))
  //      && (forall x <- s :: strLEQ(n, x))) ==> (m == n)
{
      assert forall x <- s :: x == x;
      forall x <- s ensures (strLEQ(x,x)) //by
        {
         LemmaSTREQ(x,x);
         assert strLEQ(x,x);
        }
      assert forall x <- s :: strLEQ(x,x);
      assert forall x <- s :: exists y <- s :: x == y;
      assert forall x <- s :: exists y <- s :: strLEQ(x,y);

}


function IAMTheLife(s: set<string>) : (m : string)
  requires |s| > 0
  requires exists m <- s :: forall x <- s :: strLEQ(m, x)
  requires forall m <- s, n <- s |
      (&& (forall x <- s :: strLEQ(m, x))
       && (forall x <- s :: strLEQ(n, x))) :: m == n

  ensures  forall x <- s :: strLEQ(m, x)
  {
    assert exists m <- s :: forall x <- s :: strLEQ(m, x);
    var m :| (&& (m in s)
              && (forall x <- s :: strLEQ(m,x))
              && (forall m <- s, n <- s |
                    (&& (forall x <- s :: strLEQ(m, x))
                     && (forall x <- s :: strLEQ(n, x))) :: m == n)
             );
    m
  }

///      var m :| m in s && (forall x <- s :: strLEQ(m,x);

// ghost function IAMTheLife(s: set<string>) : (m : string)
//   requires |s| > 0
//   ensures  IAMTheRessurection(s,m)
//   {
//    var mm :| mm in s && IAMTheRessurection(s,mm); mm
//   }
//
//
// lemma ThereIsOneTrueFaith(s: set<string>)
//   requires |s| > 0
//   ensures exists m <- s :: IAMTheRessurection(s, m)
//   {
//     if (|s| == 1)
//        {
//         var m := theOneAndOnly(s);
//         assert strLEQ(m,m);
//         assert forall x <- s :: x == m && strLEQ(x,m);
//         assert IAMTheRessurection(s, m);
//         assert exists m <- s :: IAMTheRessurection(s, m);
//        }
//     else
//     {
//       assert |s| > 1;
//       var guess :| guess in s;
//       var rest  := s - {guess};
//       assert s == ({guess} + rest);
//       ThereIsOneTrueFaith(rest);
//       var bestOfTHeRest := IAMTheLife(rest);
//       assert IAMTheRessurection(rest, bestOfTHeRest);
//       if (strLEQ(guess,bestOfTHeRest))
//          {
//           assert s == ({guess} + rest);
//           assert IAMTheRessurection(s, guess);
//           assert exists m <- s :: IAMTheRessurection(s, m);
//          } else {
//           assert s == ({guess} + rest);
//           assert IAMTheRessurection(s, bestOfTHeRest);
//           assert exists m <- s :: IAMTheRessurection(s, m);
//          }
//     assert exists m <- s :: IAMTheRessurection(s, m);
//     }
//  assert exists m <- s :: IAMTheRessurection(s, m);
// }


// function theOneAndOnly(s: set<string>) : (rv : string)
//   requires |s| == 1
//   ensures s == {rv}
//   ensures IAMTheRessurection({rv}, rv)
//   ensures IAMTheRessurection(s, rv)
// {
//   OneRessurection(s,rv);
//   ExtractFromSingleton(s)
// }


ghost function thereIsOneThere(s: set<string>) : string
  requires |s| > 0
  ensures thereIsOneThere(s) in s
{
  var q :| q in s;
  q
}




//probalby have to split the bloody thing tand use StrLEQIsTrans to deal with it...
function {:verify false} fmtsetstr(Y: set<string>) : string
 {
  if (|Y| < 1) then ("") else (
      assert |Y| >= 1;
      assert exists y :: y in Y;
      var y := IAMTheLife(Y);
      y + " " + fmtsetstr( Y - {y} ) )
  }



lemma TEST()
  ensures strLEQ("","")
  ensures strLEQ("3","3")
  ensures strLEQ("12345","12345")
  ensures strLEQ("","oiwr")
  ensures strLEQ("abc", "abcde")
  ensures strLEQ("a", "z")
  ensures strLEQ("ab", "z")
  ensures not(strLEQ("abc","ab"))
  ensures not(strLEQ("abzd", "abcd"))
{}

lemma STRLEQEQ(s : string)
 ensures strLEQ(s,s)
 {
  if (|s| == 0)  {assert strLEQ("",""); return; }

  assert |s| > 0;
  assert not (s[0] < s[0]);
  assert (s[0] == s[0]);
assert (strLEQ(s[1..], s[1..]));

 }

predicate strLEQ(l : string, r : string)
{
  || (|l| == 0)
  || (&& (|r| > 0)
      && (|| (l[0] < r[0])
          || ((l[0] == r[0]) && (strLEQ(l[1..], r[1..])))))
}

lemma StrEQISstrLEQ(l : string, r : string)
  requires l == r
  ensures  strLEQ(l,r)
  {}

lemma StrLEQLEQIsEQ(l : string, r : string)
  requires strLEQ(l,r)
  requires strLEQ(r,l)
  //requires (|l| == |r| <= 1)
  ensures  l == r
  ensures  r == l
  {
    if (|l| == |r| == 0) { assert l == r; return; }
    if (|l| == 0) { assert |r| > 0; assert not(strLEQ(r,l)); assert false; return; }
    if (|r| == 0) { assert |l| > 0; assert not(strLEQ(l,r)); assert false; return; }
    assert (|l| > 0) && (|r| > 0);
    if (|l| == |r| == 1) {
       if (l == r) { assert l == r; return; }
       assert {:contradiction} l != r;
       assert {:contradiction} strLEQ(l,r) != strLEQ(r,l);
       assert {:contradiction} false;
    }

//kjx not sure why I don't need a recursie case, but it seems I don't?
  }

lemma StrLEQIsTrans(a : string, b : string, c : string)
  requires strLEQ(a,b)
  requires strLEQ(b,c)
  ensures  strLEQ(a,c)
  {}


function fmtseqstr(Y: seq<string>) : string  //isnt this just a flatten?
 {
  //var Y := X;
  if (Y == []) then ("") else (
       Y[0] + " " + fmtseqstr( Y[1..] ) )
  }
//
// lemma MSSFX(s : set<string>)
//  requires |s| > 0
//  ensures  exists m <- s :: forall x <- s :: strLEQ(m, x)
//  {
//   //  var v :| IAMTheRessurection(s, v);
//   //  MSSFF(s, v);
//   //  assert exists mm <- s :: ((forall x <- s :: strLEQ(mm, x)) ==> (v == mm));
//
//   assert |s| > 0;
//   assert exists m :: m in s;
//   assert exists m <- s, x <- s :: m == x;
//
//   forall m <- s, x <- s ensures ((m == x) ==> (strLEQ(m,x)))
//     {
//       if (m == x)
//         {
//           assert (strLEQ(m,x)) == (strLEQ(x,x)) == (strLEQ(m,m)) == (strLEQ(x,m)) == true
//             by {
//               STRLEQEQ(m);
//             }
//           assert ((m == x) ==> (strLEQ(m,x)));
//         }
//         else
//         {
//           assert m != x;
//           assert ((m == x) ==> (strLEQ(m,x)));
//         }
//       assert ((m == x) ==> (strLEQ(m,x)));
//     }
//
//
//   assert exists m <- s :: exists x <- s ::   strLEQ(m,x);
//   assert forall x <- s :: exists m <- s ::   strLEQ(m,x);
//
// //  assert  exists m <- s :: IAMTheRessurection(s,m); //:: forall x <- s :: strLEQ(m, x);
//
//  assert  exists m <- s :: forall x <- s :: strLEQ(m, x);
//  }


lemma MSSFF(s : set<string>, m : string)
 requires |s| > 0
 requires IAMTheRessurection(s, m)
 ensures  forall x <- s :: strLEQ(m, x)
 ensures  exists mm <- s :: ((forall x <- s :: strLEQ(mm, x)) ==> (m == mm))
 ensures  exists m <- s :: forall x <- s :: strLEQ(m, x)
 {}

// function mss(s : set<string>) : (m : string)
//  requires |s| > 0
//  ensures  IAMTheRessurection(s,m)
// {
//   var x :| x in s && IAMTheRessurection(s,x);
//   x
// }
// by method {
//  m := minsetstr(s);
// }



lemma StringLEQ(itself : string)
 ensures strLEQ(itself,itself)
{}


method minsetstr(s : set<string>) returns (m : string)
  requires |s| > 0
  ensures  IAMTheRessurection(s,m)
{
  var t := s;
  m :| m in s;
  var z := {m};
  assert strLEQ(m,m) by { STRLEQEQ(m); }
  assert m in z;
  assert forall x <- z :: strLEQ(m,x);
  assert IAMTheRessurection(z,m);

  t := t - {m};

  while t != {}
    decreases t
    invariant IAMTheRessurection(z,m)
    invariant s == t + z
  {
    var y: string;
    y :| y in t;

assert IAMTheRessurection(z,m);
assert (m in z && forall x | x in z && strLEQ(x, m) :: strLEQ(m, x));


    if (strLEQ(y, m)) {
      assert IAMTheRessurection(z,m);
      // assert (forall x | x in (z) :: strLEQ(m, x));
      forall x <- (z) ensures ( strLEQ(m, x) )   {  }
      assert strLEQ(y, m);
      forall x <- (z) ensures ( strLEQ(y, x) )   { StrLEQ2(y,m,x); }

      // assert (forall x | x in (z) :: strLEQ(y, x));
      // assert (forall x | x in (z+{y}) :: strLEQ(y, x));
      //assert (m in (z) && forall x | x in (z+{y}) && strLEQ(x, y) ::  strLEQ(y, x));
      assert strLEQ(y,y) by { STRLEQEQ(y); }
      assert (y in (z+{y}) && forall x <- (z+{y}) :: strLEQ(y, x));
      m := y;
      assert IAMTheRessurection(z+{y},m);
     }
    else
    {
      assert not(strLEQ(y, m));
      assert strLEQ(m, y) by { StrLEQ3(y,m); }
      assert IAMTheRessurection(z,m);
      assert (m in (z+{y})  && forall x <- (z+{y}) :: strLEQ(m, x));
      assert IAMTheRessurection((z+{y}),m);
    }


    t := t - {y};
    z := z + {y};

    assert IAMTheRessurection(z,m);
  }

  assert IAMTheRessurection(t + z, m);
  assert IAMTheRessurection(s, m);
}





  /** Any totally-ordered set contains a unique minimal (equivalently, least) element. */
  lemma LemmaFindUniqueMinimal(s: set<string>) returns (min: string)
    requires |s| > 0 // TotalOrdering(R)
    ensures IAMTheRessurection(s, min) // && (forall min' <- s | IAMTheRessurection(s, min') :: min == min')
  {
    var x :| x in s;
    if s == {x} {
      min := x;
      StrLEQ4(x);
      StrLEQ4(min);
    assert IAMTheRessurection({x}, min);
    assert IAMTheRessurection(s, min);
    // StrLEQ1(min, x);
    // StrLEQ3(min, x);
    // StrLEQ4(min);
    // StrLEQ4(x);
    } else {
      var min' := LemmaFindUniqueMinimal(s - {x});
      assert IAMTheRessurection(s - {x}, min');
      assert forall q <- (s - {x}) :: strLEQ(min', q);
      assert min' in (s - {x});
      StrLEQ3(min', x);
      if
      case strLEQ(min', x) =>
          assert forall q <- (s - {x}) :: strLEQ(min', q);
          assert strLEQ(min', x);
          assert forall q <- (s - {x} + {x}) :: strLEQ(min', q);
          assert (s - {x}) + {x} == s;
          assert forall q <- (s) :: strLEQ(min', q);
          min := min';
          assert forall q <- (s) :: strLEQ(min', q);
          assert min in s;
          assert forall q <- s :: strLEQ(min, q);
          assert IAMTheRessurection(s, min);

      case strLEQ(x, min') => min := x;
          assert forall q <- (s - {x}) :: strLEQ(min', q);
          forall q <- (s - {x}) ensures strLEQ(min, q)
            {
              assert strLEQ(min', q);
              assert strLEQ(min, min');
              StrLEQ2(min, min',q);
            }
          StrLEQ4(x);
          assert min == x;
          assert strLEQ(min, x);
          StrLEQ4(min);
          assert (s - {x}) + {x} == s;
          assert IAMTheRessurection(s, min);
    }
    assert IAMTheRessurection(s, min);
  }
