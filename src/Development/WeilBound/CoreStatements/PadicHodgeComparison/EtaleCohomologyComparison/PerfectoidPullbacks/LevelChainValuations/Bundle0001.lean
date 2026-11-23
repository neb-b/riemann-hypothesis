module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ToBSurj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0001
public import GroundTheory.PAdicHodge.UntiltFrobeniusEquivSymmEpsilonNeOne
public import GroundTheory.PAdicHodge.BdRAlgCl
public import GroundTheory.PAdicHodge.BdRGalois
public import GroundTheory.PAdicHodge.BdRField

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

section
variable (L : Lev R m) (M : Model l K) (s : ℕ)

abbrev QA : ObjectProperty (Thick (nlFun L.γ 0 M.X M.p (κA (OK l K) L.I))) := TS L.γ M.p l s {⊤}

abbrev QB : ObjectProperty (Thick (nlFun L.γB 0 M.gen M.q (κA K L.IB))) := TS L.γB M.q 1 s {⊤}


variable {L} in
def nmB (hL : L.Good) : NMor L.γ M.p (κA (OK l K) L.I) L.γB M.q (κA K L.IB) L.ι where
  hI := hL.ι_dp
  u := pullback.fst _ _
  g := (OK l K).subtype
  hu := pullback.condition
  hκ a r h := by
    have h1 : algebraMap (OK l K) L.A a - r ∈ L.I := Ideal.Quotient.eq.1 h
    rw [hL.ι_I, Ideal.mem_comap, map_sub, hL.ι_O] at h1
    exact Ideal.Quotient.eq.2 h1


variable {L} in
def smB (hL : L.Good) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    SMor (sP (QA L M s)) (sP (QB L M s)) L.ι :=
  (nmB M hL).smor (QA L M s) (QB L M s) hQ


variable {L} in
def bMap (hL : L.Good) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) (j : ℕ) :
    HO (QA L M s) j →ₛₗ[L.ι] HO (QB L M s) j :=
  (smB M s hL hQ).o.pull j

end

def Lev.CrisOK {m : ℕ} (L : Lev (per l K) m) : Prop :=
  L.lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ L.I ∧
  ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a →
    algebraMap (OK l K) L.A a - L.lam (algebraMap (Ainf l) (Acris l) w) ∈ L.I

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))

def chainOf (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j) :
    Chain.{1} (per l K).A L.A L.B K where
  ℓ := l
  S n j := M.Hc false n j
  Zn n j := HM (QA L M s) none ((l : L.A) ^ n) j
  Z j := HO (QA L M s) j
  W j := HO (QB L M s) j
  V j := HdR M.q j
  lam := L.lam
  ι := L.ι
  o := algebraMap K L.B
  tS n j := (M.HS false j).r n
  tZ n j := trM (QA L M s) none (l : L.A) n j
  r := rH
  red n j := redM (QA L M s) none ((l : L.A) ^ n) j
  b j := bMap M s hL hQ j
  μ j := muB L.γB M.q 1 s {⊤} j

end

end CrystallineSemistableComparison.Pb.Kap
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.FinDefs
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

set_option maxHeartbeats 1000000

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K}

structure RhoSys (S : LevSys R) (G : Model l K → Prop) (D : Dat R) (c1K : ∀ {M : Model l K}, D.Ch M → HdR M.q 2 → Prop) where
  ρ : ∀ {M : Model l K} (a : D.Ch M) (j m : ℕ), (D.H a).N j → (Module.Dual K (HdR M.q j) →+ (S.L m).B) → Prop
  ex : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x, ∃ f, ρ a j m x f
  uniq : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x f f', ρ a j m x f → ρ a j m x f' → f = f'
  add : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x y f g, ρ a j m x f → ρ a j m y g → ρ a j m (x + y) (f + g)
  smul : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m (c : R.A) x f, ρ a j m x f →
    ρ a j m (c • x) ((AddMonoidHom.mulLeft ((S.L m).ι ((S.L m).lam c))).comp f)
  lin' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x f, ρ a j m x f → ∀ (k : K) φ, f (k • φ) = algebraMap K (S.L m).B k * f φ
  lev : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x f, ρ a j (m + 1) x f → ρ a j m x ((S.dB m).toAddMonoidHom.comp f)
  act : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m (g : K.fixingSubgroup) x f, ρ a j m x f →
    ρ a j m ((D.H a).act j g x) (((S.L m).σB g).toAddMonoidHom.comp f)
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N} (μ : D.Mo u hu a b), G M → G N →
    ∀ j m x f f', ρ b j m x f → ρ a j m (D.pullH μ j x) f' →
      ∀ φ, f' φ = f (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu))
  fil : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j m x f, ρ a j m x f → ∀ n r : ℕ, n ≤ m → D.fil a j n x →
    ∀ φ : Module.Dual K (HdR M.q j), (∀ h ∈ FilR M.q j (r + 1), φ h = 0) → f φ ∈ pdP (S.L m).γB (n - r)
  cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} m x y z f g h, ρ a i m x f → ρ a j m y g → ρ a (i + j) m z h →
    (D.H a).cup x y z → ∀ {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i)) (b' : Module.Basis (Fin e') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K (S.L m).B (φ (cupK M.q rfl (b s) (b' s')))
  one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ m x f, ρ a 0 m x f → (D.H a).one x → ∀ φ, f φ = algebraMap K (S.L m).B (φ (oneK M.q))
  c1 : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ m x f c, ρ a 2 m x f → D.c1H a x → c1K a c → ∀ φ, f φ = algebraMap K (S.L m).B (φ c)

structure KapA (G : Model l K → Prop) (D : Dat R) (c1K : ∀ {M : Model l K}, D.Ch M → HdR M.q 2 → Prop) where
  κ : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ), (D.H a).N j →+ (Module.Dual K (HdR M.q j) →+ R.B)
  lin : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (c : R.A) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j (c • x) φ = R.i c * κ a j x φ
  lin' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (k : K) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j x (k • φ) = R.o k * κ a j x φ
  act : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (σ : K.fixingSubgroup) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j ((D.H a).act j σ x) φ = R.σ σ (κ a j x φ)
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}
    (m : D.Mo u hu a b), G M → G N → ∀ (j : ℕ) (x : (D.H b).N j) (φ : Module.Dual K (HdR M.q j)),
    κ a j (D.pullH m j x) φ = κ b j x (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu))
  fil : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j n r : ℕ) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), D.fil a j n x → (∀ h ∈ FilR M.q j (r + 1), φ h = 0) →
    ∃ y ∈ R.P, R.tB ^ r * κ a j x φ = R.tB ^ n * y
  cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : (D.H a).N i) (y : (D.H a).N j)
    (z : (D.H a).N (i + j)), (D.H a).cup x y z →
    ∀ {m m' : ℕ} (b : Module.Basis (Fin m) K (HdR M.q i)) (b' : Module.Basis (Fin m') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      κ a (i + j) z φ = ∑ s, ∑ s', κ a i x (b.coord s) * κ a j y (b'.coord s') * R.o (φ (cupK M.q rfl (b s) (b' s')))
  one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ x : (D.H a).N 0, (D.H a).one x →
    ∀ φ : Module.Dual K (HdR M.q 0), κ a 0 x φ = R.o (φ (oneK M.q))
  c1 : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (x : (D.H a).N 2) (c : HdR M.q 2), D.c1H a x → c1K a c →
    ∀ φ : Module.Dual K (HdR M.q 2), κ a 2 x φ = R.o (φ c)

end CrystallineSemistableComparison.Pb.Kap
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.Pb.Lat

variable (l : ℕ) [Fact l.Prime]

abbrev Bk (k : ℕ) : Type := BdRp l ⧸ Ideal.span {tBdR l ^ k}

def fk (k : ℕ) : Ainf l →+* Bk l k := (Ideal.Quotient.mk _).comp (wittToBDeRhamPlus (normInteger ℂ_[l]) l)

def dk (k : ℕ) : Bk l (k + 1) →+* Bk l k :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ k)))

def pk (k : ℕ) : BdRp l →+* Bk l k := Ideal.Quotient.mk _

def pInv : ↥(algebraMap (BdRp l) (BdR l)).range →+* BdRp l :=
  (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm.toRingHom

def kP (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : K →+* BdRp l := (algClToBdR l).toRingHom.comp K.val.toRingHom

def gP {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (g : K.fixingSubgroup) : BdRp l →+* BdRp l := galBdRHom (toBot g.1)

structure LevHyp (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : ℕ) : Prop where
  ok : ∀ (k : ℕ) (a : OK l K), pk l k (kP l K a) ∈ sub (fk l k) (xi0 l) l M
  cris : ∀ (k : ℕ) (c : Acris l), pk l k (ACris.iota ℂ_[l] l c) ∈ sub (fk l k) (xi0 l) l M
  hc : ∀ k : ℕ, DPClosed (ι (fk l k) (xi0 l) l M) (γB (fk l k) (xi0 l))
  galT : ∀ (k : ℕ) (g : K.fixingSubgroup), Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (gP l g)
  gal : ∀ (k : ℕ) (g : K.fixingSubgroup), ∀ x ∈ sub (fk l k) (xi0 l) l M,
    Ideal.quotientMap _ (gP l g) (galT k g) x ∈ sub (fk l k) (xi0 l) l M
  dIn : ∀ k : ℕ, ∀ x ∈ sub (fk l (k + 1)) (xi0 l) l M, dk l k x ∈ sub (fk l k) (xi0 l) l M

variable {l} {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

def okA (h : LevHyp l K M) (k : ℕ) : OK l K →+* A (fk l k) (xi0 l) l M :=
  ((pk l k).comp ((kP l K).comp (OK l K).subtype)).codRestrict (sub (fk l k) (xi0 l) l M) (h.ok k)

def lamA (h : LevHyp l K M) (k : ℕ) : Acris l →+* A (fk l k) (xi0 l) l M :=
  ((pk l k).comp (ACris.iota ℂ_[l] l)).codRestrict (sub (fk l k) (xi0 l) l M) (h.cris k)

def gB (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) : Bk l k →+* Bk l k :=
  Ideal.quotientMap _ (gP l g) (h.galT k g)

def lev (h : LevHyp l K M) (k : ℕ) : Kap.Lev (per l K) k where
  B := Bk l k
  balg := ((pk l k).comp (kP l K)).toAlgebra
  toB := (pk l k).comp (pInv l)
  IB := IB (fk l k) (xi0 l)
  γB := γB (fk l k) (xi0 l)
  A := A (fk l k) (xi0 l) l M
  aalg := (okA h k).toAlgebra
  I := I (fk l k) (xi0 l) l M
  γ := γ (fk l k) (xi0 l) l M (h.hc k)
  ι := ι (fk l k) (xi0 l) l M
  lam := lamA h k
  σA g := map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g)
  σB g := gB h k g

def levSys (h : LevHyp l K M) : Kap.LevSys (per l K) where
  L m := lev h (m + 1)
  dA m := map (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1)) (h.dIn (m + 1))
  dB m := dk l (m + 1)

end CrystallineSemistableComparison.Pb.Lat
end
end

