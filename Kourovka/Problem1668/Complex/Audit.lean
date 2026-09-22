import WordMaps

/-! Publication audit for the preserved Kourovka 16.68 proof. -/

/-- info: 'WordMaps.word_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WordMaps.word_surjective

/-- info: 'WordMaps.complex_word_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WordMaps.complex_word_surjective
