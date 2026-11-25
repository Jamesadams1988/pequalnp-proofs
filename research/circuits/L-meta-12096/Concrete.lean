import Rectangle

namespace Row12096Rectangle.Concrete
open Row12096Signed

def state : State := (branch (branch (branch (branch (branch (branch first 0 5 1 3) 0 1 1 2) 3 6 2 3) 3 4 1 2) 2 4 3 0) 1 2 0 0)

def packed : Array Nat := #[0x0, 0x2b52cbf8a, 0x278659bc9, 0x2a72d9b88, 0x2762cbf49, 0x2b32cbf08, 0x2672dab48, 0x6272dbb08, 0x278a697c9, 0x2972e9788, 0x2586773c7, 0x2892f7386, 0x2572ea748, 0xa172eb708, 0x24a2f7345, 0xe072f7345, 0x27634dec9, 0x2b32cde88, 0x26735cac8, 0x2a32dda88, 0x2732cee48, 0x3332cfe49, 0x2632dea48, 0x6232dfa49, 0x25736c6c8, 0x2932ed688, 0x24c3772c3, 0x2892f72c3, 0x2532ee648, 0xa132ef649, 0x24a2f72c3, 0xe032f72c3, 0xf82cbdc3, 0x2892cbdc3, 0x4e82d9bc9, 0x4c92d9b88, 0x24a2cbdc3, 0x30934bdc3, 0x4ca2dab48, 0x5c935bb08, 0x8d82e97c9, 0x8c92e9788, 0xccc2f93c9, 0xcc92f9388, 0x8ca2ea748, 0x9c936b708, 0xcca2fa348, 0xd8937b349, 0x1f82cddc5, 0x2892cddc5, 0x5e82dcac8, 0x5c92dda88, 0x24a2cedc6, 0x60964fdc7, 0x5ca2dea48, 0xe09a5fa49, 0x9d82ec6c8, 0x9c92ed688, 0xcca2fc2c8, 0xd892fd2c9, 0x9ca2ee648, 0xe0966f649, 0xd4a2fe2ca, 0x0]
def tripleAt (code base : Nat) : Triple :=
  let r (j : Nat) : Fin 64 := ⟨(code / 2^(base+6*j))%64, by omega⟩
  (rowPosition (r 0), rowPosition (r 1), rowPosition (r 2))
def certificate (a _b : List W) : Triple × Triple :=
  let key := state.2.foldr (fun w acc => acc*2 + (a.contains w).toNat) 0
  let code := packed[key]?.getD 0
  (tripleAt code 0, tripleAt code 18)

set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem zeroSlack : state.1 = 0 := by decide +kernel
theorem guards : cuts state.2 = -1 ∧ state.2.Nodup ∧ state.2.length = 6 := by decide +kernel
theorem certificate_valid : checkAll state.2 certificate = true := by decide +kernel

theorem noSplit (A B : List W) (ha : A ≠ []) (hb : B ≠ []) (h : (A ++ B).Perm state.2)
    (g u v : W) (pol : g = goal ∨ g = ~~~goal) (du : depends A u) (dv : depends B v) :
    g ≠ u &&& v := excludes_split certificate_valid A B ha hb h g u v pol du dv

end Row12096Rectangle.Concrete
#print axioms Row12096Rectangle.Concrete.noSplit
