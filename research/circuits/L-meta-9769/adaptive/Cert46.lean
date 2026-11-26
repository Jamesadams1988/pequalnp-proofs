import Graph

namespace ProjectiveEdge.Cert46
open ProjectiveEdge.Adaptive ProjectiveEdge.Instance Row9769.Elimination PEqualNP.MetaComplexity
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

theorem node0 : Bound graph (members 4183295983615) 36 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node1 : Bound graph (members 4183295971167) 32 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node2 : Bound graph (members 4191885918207) 38 := by
  exact branch (v := 33) (N := members 12448) (Z := members 4183295983615) (O := members 4183295971167) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node0 node1

theorem node3 : Bound graph (members 1992862104319) 32 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node4 : Bound graph (members 1992861047542) 28 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node5 : Bound graph (members 4191885359871) 34 := by
  exact branch (v := 41) (N := members 1056777) (Z := members 1992862104319) (O := members 1992861047542) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node3 node4

theorem node6 : Bound graph (members 4260605394943) 40 := by
  exact branch (v := 36) (N := members 558336) (Z := members 4191885918207) (O := members 4191885359871) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node2 node5

theorem node7 : Bound graph (members 2061580957182) 32 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node8 : Bound graph (members 1786367505918) 29 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node9 : Bound graph (members 2061580957183) 34 := by
  exact branch (v := 0) (N := members 275213451264) (Z := members 2061580957182) (O := members 1786367505918) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node7 node8

theorem node10 : Bound graph (members 2061580899830) 28 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node11 : Bound graph (members 908382180854) 24 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node12 : Bound graph (members 2061580916214) 30 := by
  exact branch (v := 14) (N := members 1153198718976) (Z := members 2061580899830) (O := members 908382180854) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node10 node11

theorem node13 : Bound graph (members 4260604212735) 36 := by
  exact branch (v := 41) (N := members 40969) (Z := members 2061580957183) (O := members 2061580916214) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node9 node12

theorem node14 : Bound graph (members 4398044348415) 42 := by
  exact branch (v := 37) (N := members 1182208) (Z := members 4260605394943) (O := members 4260604212735) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node6 node13

theorem node15 : Bound graph (members 1984263258111) 32 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node16 : Bound graph (members 1945604358143) 29 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node17 : Bound graph (members 1984263290879) 34 := by
  exact branch (v := 15) (N := members 38658899968) (Z := members 1984263258111) (O := members 1945604358143) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node15 node16

theorem node18 : Bound graph (members 884751622134) 28 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node19 : Bound graph (members 884751077362) 24 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node20 : Bound graph (members 1984263249910) 30 := by
  exact branch (v := 40) (N := members 544772) (Z := members 884751622134) (O := members 884751077362) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node18 node19

theorem node21 : Bound graph (members 4183286546431) 36 := by
  exact branch (v := 41) (N := members 40969) (Z := members 1984263290879) (O := members 1984263249910) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node17 node20

theorem node22 : Bound graph (members 334827552767) 28 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node23 : Bound graph (members 334827280381) 24 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node24 : Bound graph (members 884583366655) 30 := by
  exact branch (v := 39) (N := members 272386) (Z := members 334827552767) (O := members 334827280381) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node22 node23

theorem node25 : Bound graph (members 334743404543) 25 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node26 : Bound graph (members 25505759231) 23 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node27 : Bound graph (members 334743666687) 27 := by
  exact branch (v := 18) (N := members 309237645312) (Z := members 334743404543) (O := members 25505759231) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node25 node26

theorem node28 : Bound graph (members 884583890943) 32 := by
  exact branch (v := 19) (N := members 549839699968) (Z := members 884583366655) (O := members 334743666687) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node24 node27

theorem node29 : Bound graph (members 4183287595007) 38 := by
  exact branch (v := 20) (N := members 3298702655488) (Z := members 4183286546431) (O := members 884583890943) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node21 node28

theorem node30 : Bound graph (members 4398044413951) 44 := by
  exact branch (v := 16) (N := members 214756753408) (Z := members 4398044348415) (O := members 4183287595007) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node14 node29

theorem node31 : Bound graph (members 2680056889325) 32 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node32 : Bound graph (members 2680056855277) 29 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node33 : Bound graph (members 2748776366061) 34 := by
  exact branch (v := 36) (N := members 34048) (Z := members 2680056889325) (O := members 2680056855277) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node31 node32

theorem node34 : Bound graph (members 2679973003244) 29 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node35 : Bound graph (members 205803405292) 26 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node36 : Bound graph (members 2679973003245) 31 := by
  exact branch (v := 0) (N := members 2474169597952) (Z := members 2679973003244) (O := members 205803405292) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node34 node35

theorem node37 : Bound graph (members 2748776890349) 36 := by
  exact branch (v := 19) (N := members 68803362816) (Z := members 2748776366061) (O := members 2679973003245) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node33 node36

theorem node38 : Bound graph (members 2748775045100) 28 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node39 : Bound graph (members 412145063916) 24 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node40 : Bound graph (members 2748776093676) 30 := by
  exact branch (v := 20) (N := members 2336629981184) (Z := members 2748775045100) (O := members 412145063916) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node38 node39

theorem node41 : Bound graph (members 274538338284) 24 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node42 : Bound graph (members 136931612652) 21 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node43 : Bound graph (members 274539386860) 26 := by
  exact branch (v := 20) (N := members 137606725632) (Z := members 274538338284) (O := members 136931612652) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node41 node42

theorem node44 : Bound graph (members 2748776093677) 32 := by
  exact branch (v := 0) (N := members 2474236706816) (Z := members 2748776093676) (O := members 274539386860) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node40 node43

theorem node45 : Bound graph (members 3298532704237) 38 := by
  exact branch (v := 39) (N := members 796672) (Z := members 2748776890349) (O := members 2748776093677) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node37 node44

theorem node46 : Bound graph (members 1099507838952) 28 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node47 : Bound graph (members 992129462248) 24 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node48 : Bound graph (members 1099507871720) 30 := by
  exact branch (v := 15) (N := members 107378376704) (Z := members 1099507838952) (O := members 992129462248) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node46 node47

theorem node49 : Bound graph (members 549752016864) 25 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node50 : Bound graph (members 549751752672) 23 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node51 : Bound graph (members 1099507830752) 27 := by
  exact branch (v := 39) (N := members 264192) (Z := members 549752016864) (O := members 549751752672) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node49 node50

theorem node52 : Bound graph (members 3298531127272) 32 := by
  exact branch (v := 41) (N := members 40968) (Z := members 1099507871720) (O := members 1099507830752) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node48 node51

theorem node53 : Bound graph (members 274538344424) 24 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node54 : Bound graph (members 240136663016) 21 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node55 : Bound graph (members 274538606568) 26 := by
  exact branch (v := 18) (N := members 34401681408) (Z := members 274538344424) (O := members 240136663016) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node53 node54

theorem node56 : Bound graph (members 137099380712) 21 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node57 : Bound graph (members 137099249128) 19 := by
  exact leaf (by unfold Live; decide +kernel) (by decide +kernel)

theorem node58 : Bound graph (members 274538334184) 23 := by
  exact branch (v := 37) (N := members 131584) (Z := members 137099380712) (O := members 137099249128) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node56 node57

theorem node59 : Bound graph (members 824294420456) 28 := by
  exact branch (v := 39) (N := members 272384) (Z := members 274538606568) (O := members 274538334184) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node55 node58

theorem node60 : Bound graph (members 3298531127273) 34 := by
  exact branch (v := 0) (N := members 2474236706816) (Z := members 3298531127272) (O := members 824294420456) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node52 node59

theorem node61 : Bound graph (members 4398044332013) 40 := by
  exact branch (v := 40) (N := members 1576964) (Z := members 3298532704237) (O := members 3298531127273) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node45 node60

theorem node62 : Bound graph (members 4398046511103) 46 := by
  exact branch (v := 21) (N := members 81938) (Z := members 4398044413951) (O := members 4398044332013) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) node30 node61

theorem lower (s : ℕ) (h : HasCircuitSize 42 literal s) : 46 ≤ s := literalBridge _ node62 _ h
end ProjectiveEdge.Cert46
#print axioms ProjectiveEdge.Cert46.lower
