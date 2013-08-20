procedure {:yields} {:stable} A();
procedure {:yields} {:stable} B();
procedure {:yields} C() { call A() | B(); }
