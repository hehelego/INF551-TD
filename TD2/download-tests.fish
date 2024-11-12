set sat_tests \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/SAT/ais12.cnf' \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/SAT/flat50-1000.cnf' \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/SAT/ii8a2.cnf' \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/SAT/quinn.cnf' \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/SAT/zebra_v155_c1135.cnf'

set unsat_tests \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/UNSAT/aim-50-1_6-no-1.cnf' \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/UNSAT/bf1355-075.cnf' \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/UNSAT/dubois20.cnf' \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/UNSAT/dubois21.cnf' \
    'https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/doc/cnf/UNSAT/hole6.cnf'

for f in $sat_tests
    echo "Downloading $f"
    curl -O $f
end

for f in $unsat_tests
    echo "Downloading $f"
    curl -O $f
end
