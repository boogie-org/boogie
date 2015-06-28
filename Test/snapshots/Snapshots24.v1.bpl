procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "2"} M()
{
    if (*)
    {
        assert {:subsumption 0} 1 == 1;
    }
    else if (*)
    {
        assert {:subsumption 1} 5 == 5;
    }
    else if (*)
    {
        assert {:subsumption 2} 6 != 6;  // error
    }
    else
    {
        assert {:subsumption 1} 2 == 2;
        assert {:subsumption 2} 4 == 4;
        assert 5 == 5;
    }

    assert {:subsumption 0} 3 == 3;
}
