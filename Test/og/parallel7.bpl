procedure {:yields} {:stable} A();
procedure {:yields} {:stable} B();
procedure {:yields} C() { par A() | B(); }
