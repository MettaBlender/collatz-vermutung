from collatz_verteilung import besuche_naiv, besuche_zaehlen, collatz_folge


def test_folge_von_6():
    assert collatz_folge(6) == [6, 3, 10, 5, 16, 8, 4, 2, 1]


def test_schnell_gleich_naiv():
    for ziel in (1, 2, 7, 27, 500):
        assert besuche_zaehlen(ziel) == dict(besuche_naiv(ziel))


def test_eins_kommt_in_jeder_folge_vor():
    assert besuche_zaehlen(1000)[1] == 1000
