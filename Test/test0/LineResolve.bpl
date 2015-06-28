// RUN: %boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
procedure P() {
var x: int;
x :=

 a+  // error: LineResolve.bpl(5,1)

  b+  // error: LineResolve.bpl(7,2)
#line 12
c+ // error: LineResolve.bpl(12,0)
          d+ // error: LineResolve.bpl(13,10)
#line 12
e+ // error: LineResolve.bpl(12,0)
#line 2
f+ // error: LineResolve.bpl(2,0)
#line    1000          
#line 900
g+ // error: LineResolve.bpl(900,0)

#line 10    Abc.txt

   h+   // error: Abc.txt(11,3)

i+ // error: Abc.txt(13,0)
#line 98

j+  // error: Abc.txt(99,0)

#line                103       c:\Users\leino\Documents\Programs\MyClass.ssc  

k+ // error: c:\Users\leino\Documents\Programs\MyClass.ssc(104,0)

#line -58

#line 12 A B C . txt     
l+  // error: A B C . txt(12,0)

0;
}

#line 100 LineResolve.bpl
procedure ResolutionTest() {
  x := 0;  // error: undeclared identifier (once upon a time, this used to crash Boogie)
}
