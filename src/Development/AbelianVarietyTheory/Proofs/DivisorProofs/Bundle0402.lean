module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0376
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E), (∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k))))) → ∀ n : ℤ, Function.Bijective (fun (x : H R E F n) (i : ι) => pull R (a i) F n x) := by
  first | (exact @GlobalTheory.EtC.HCofan.main) | (exact GlobalTheory.EtC.HCofan.main) | (intros; apply GlobalTheory.EtC.HCofan.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpen
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CechDR

variable {X X' : Scheme.{0}}

theorem Pair.exists_basicOpen (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (f : Γ(X', W.1)), p.1.1.1 = X'.basicOpen f ∧ x ∈ p.1.1.1 := by
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show φ.base x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨f, hf, hxf⟩ := W.2.exists_basicOpen_le (V := W.1 ⊓ φ ⁻¹ᵁ U) ⟨x, hx, hxU⟩ hx
  exact ⟨⟨(⟨X'.basicOpen f, W.2.basicOpen f⟩, ⟨U, hU⟩), hf.trans inf_le_right⟩, f, rfl, hxf⟩

theorem Pair.exists_le_le (φ : X' ⟶ X) (p q : Pair φ) {x : X'} (hx : x ∈ p.1.1.1 ⊓ q.1.1.1) :
    ∃ r : Pair φ, r ≤ p ∧ r ≤ q ∧ x ∈ r.1.1.1 := by
  have hy : φ.base x ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hx.1, q.2 hx.2⟩
  obtain ⟨U, hU, hxU, hUle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hy
  obtain ⟨U', hU', hxU', hU'le⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ φ ⁻¹ᵁ U from ⟨hx, hxU⟩)
  refine ⟨⟨(⟨U', hU'⟩, ⟨U, hU⟩), hU'le.trans inf_le_right⟩, ?_, ?_, hxU'⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_left), hUle.trans inf_le_left⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_right), hUle.trans inf_le_right⟩

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem Pair.exists_le (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (hp : p.1.1 ≤ W), x ∈ p.1.1.1 := by
  obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
  exact ⟨p, show p.1.1.1 ≤ W.1 from e ▸ X'.basicOpen_le f, hxp⟩

theorem sec_eq_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens)
    (a b : (OAff s').obj (op W))
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op a = mp (OAff s') (homOfLE hp).op b) :
    a = b := by
  refine TopCat.Presheaf.section_ext X'.sheaf W.1 a b fun x hx ↦ ?_
  obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
  have e : (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom a) =
      (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom b) :=
    congrArg _ (h p hp)
  have k := X'.presheaf.germ_res (homOfLE (show p.1.1.1 ≤ W.1 from hp)) x hxp
  exact (congrArg (fun t ↦ t.hom a) k).symm.trans (e.trans (congrArg (fun t ↦ t.hom b) k))

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBisimplicialShuffleOperatorsStatement
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bisimplicial_shuffle_operators : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧ ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  first | (exact @GlobalTheory.EZ.Shuf.exists_shuffle) | (exact GlobalTheory.EZ.Shuf.exists_shuffle) | (intros; apply GlobalTheory.EZ.Shuf.exists_shuffle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBaseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  first | (exact @GlobalTheory.EtC.GmStep.cechDiag_spec) | (exact GlobalTheory.EtC.GmStep.cechDiag_spec) | (intros; apply GlobalTheory.EtC.GmStep.cechDiag_spec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainMapOfFibreCocyclePairing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC.PsiModel
variable {R : Type} [CommRing R]

theorem map_sres {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sx.map f (Sx.res g x) = Sx.res g (Sx.map f x) := by
  unfold Sx.map Sx.res
  exact NatTrans.naturality_apply (f.app (op (SimplexCategory.mk p))) g.op x

theorem map_face {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    Sx.map f (Sx.face x i) = Sx.face (Sx.map f x) i := by
  unfold Sx.map Sx.face
  have h1 := NatTrans.congr_app (f.naturality (SimplexCategory.δ i).op) (op U)
  simp only [NatTrans.comp_app] at h1
  have h2 := ConcreteCategory.congr_hom h1 x
  simp only [ConcreteCategory.comp_apply] at h2
  exact h2

theorem map_map {E E' E'' : Spc} (f : E ⟶ E') (f' : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    Sx.map f' (Sx.map f x) = Sx.map (f ≫ f') x := rfl

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  simp [Sec.res]

theorem ev_smul {E : Spc} {I : Cx R} {n : ℤ} (r : ULift.{1} R) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (R := R) (r • α) p s h U x = r • ev (R := R) α p s h U x := by
  rw [ev_def, ev_def, Cochain.smul_v, Linear.comp_smul]
  rfl

variable {q N : ℕ}

def fstH {U V : Scheme.{0}} {p : ℕ} (y : Sx (sch.obj U ⨯ fibQ q N) p V) : V ⟶ U :=
  Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y

theorem fstH_res {U V' V : Scheme.{0}} {p : ℕ} (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V) :
    fstH (Sx.res g y) = g ≫ fstH y := by
  unfold fstH
  rw [map_sres]
  rfl

theorem fstH_face {U V : Scheme.{0}} {p : ℕ} (y : Sx (sch.obj U ⨯ fibQ q N) (p + 1) V) (i : Fin (p + 2)) :
    fstH (Sx.face y i) = fstH y := by
  unfold fstH
  rw [map_face]
  rfl

theorem fstH_map {U U' V : Scheme.{0}} {p : ℕ} (g : U' ⟶ U) (y : Sx (sch.obj U' ⨯ fibQ q N) p V) :
    fstH (Sx.map (prod.map (sch.map g) (𝟙 (fibQ q N))) y) = fstH y ≫ g := by
  unfold fstH
  rw [map_map, prod.map_fst]
  rfl

theorem snd_map {U U' V : Scheme.{0}} {p : ℕ} (g : U' ⟶ U) (y : Sx (sch.obj U' ⨯ fibQ q N) p V) :
    Sx.map (prod.snd : sch.obj U ⨯ fibQ q N ⟶ _) (Sx.map (prod.map (sch.map g) (𝟙 (fibQ q N))) y) = Sx.map prod.snd y := by
  rw [map_map, prod.map_snd, Category.comp_id]

variable {I₁ I₂ K : Cx R} (μ : Pair I₁ I₂ K) {n : ℤ} (z : Cochain ((chains R).obj (fibQ q N)) I₂ n)

def pval {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V) : Sec (K.X s) V :=
  μ.mul V m (-(p : ℤ) + n) s (by omega) (Sec.res (fstH y) a) (ev (R := R) z p (-(p : ℤ) + n) rfl V (Sx.map prod.snd y))

theorem pval_res {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    {V' V : Scheme.{0}} (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V) :
    Sec.res g (pval μ z hw a p s hs V y) = pval μ z hw a p s hs V' (y.res g) := by
  unfold pval
  rw [μ.nat, res_res, ev_res, map_sres, fstH_res]

def cval {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) :
    Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) K w :=
  (CupSpec.ev_exists (pval μ z hw a) (fun p s hs V' V g y => pval_res μ z hw a p s hs g y)).choose

theorem cval_ev {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V) : ev (R := R) (cval μ z hw a) p s hs V y = pval μ z hw a p s hs V y :=
  (CupSpec.ev_exists (pval μ z hw a) (fun p s hs V' V g y => pval_res μ z hw a p s hs g y)).choose_spec p s hs V y

theorem cval_add {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a b : Sec (I₁.X m) U) :
    cval μ z hw (a + b) = cval μ z hw a + cval μ z hw b := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_add, cval_ev, cval_ev, cval_ev]
  unfold pval
  rw [show Sec.res (fstH y) (a + b) = Sec.res (fstH y) a + Sec.res (fstH y) b from map_add _ _ _, LinearMap.map_add₂]

theorem cval_smul {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (r : ULift.{1} R) (a : Sec (I₁.X m) U) :
    cval μ z hw (r • a) = r • cval μ z hw a := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_smul, cval_ev, cval_ev]
  unfold pval
  rw [show Sec.res (fstH y) (r • a) = r • Sec.res (fstH y) a from map_smul _ _ _, LinearMap.map_smul₂]

theorem cval_nat {U U' : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (g : U' ⟶ U) (a : Sec (I₁.X m) U) :
    cval μ z hw (Sec.res g a) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (cval μ z hw a) (zero_add w) := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_pull, cval_ev, cval_ev]
  unfold pval
  rw [fstH_map, snd_map, res_res]

def pmor {m w : ℤ} (hw : m + n = w) : (I₁.X m).obj ⟶ cotPre R q N K w where
  app U := ModuleCat.ofHom
    { toFun := fun a => cval μ z hw (U := U.unop) a
      map_add' := cval_add μ z hw
      map_smul' := cval_smul μ z hw }
  naturality U U' f := by
    ext a : 2
    exact cval_nat μ z hw f.unop a

def smor {m w : ℤ} (hw : m + n = w) : I₁.X m ⟶ (Jcx R q N K).X w :=
  ObjectProperty.homMk (pmor μ z hw ≫ toSheafify Scheme.etaleTopology.{0} (cotPre R q N K w))

def psiC : Cochain I₁ (Jcx R q N K) n := Cochain.mk fun m w hw => smor μ z hw

theorem psiC_v {m w : ℤ} (hw : m + n = w) : (psiC μ z).v m w hw = smor μ z hw := Cochain.mk_v _ _ _ _

theorem Jcx_d (w : ℤ) : (Jcx R q N K).d w (w + 1) = (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N K w) := by
  simp [Jcx]

theorem mul_d_congr {V : Scheme.{0}} {m T t1 t2 w : ℤ} (e : t1 = t2) (h1 : m + t1 = w) (h2 : m + t2 = w)
    (A : Sec (I₁.X m) V) (B : Sec (I₂.X T) V) :
    μ.mul V m t1 w h1 A (Sec.map (I₂.d T t1) B) = μ.mul V m t2 w h2 A (Sec.map (I₂.d T t2) B) := by
  subst e
  rfl

theorem cval_δ (hn : Even n) (hz : δ n (n + 1) z = 0) {U : Scheme.{0}} {m w w' : ℤ} (hw : m + n = w)
    (hw' : m + 1 + n = w') (a : Sec (I₁.X m) U) :
    δ w w' (cval μ z hw a) = cval μ z hw' (Sec.map (I₁.d m (m + 1)) a) := by
  have hww : w + 1 = w' := by omega
  refine ev_ext _ _ fun k t ht V y => ?_
  rcases k with _ | k
  · rw [ev_δ_zero hww _ V w t (by simp) ht y, cval_ev, cval_ev]
    unfold pval
    obtain rfl : t = w + 1 := by simp at ht; omega
    rw [μ.leibniz]
    have hz0 : Sec.map (I₂.d (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + n + 1))
        (ev (R := R) z 0 (-((0 : ℕ) : ℤ) + n) rfl V (Sx.map prod.snd y)) = 0 := by
      rw [← ev_δ_zero (n := n) (m := n + 1) rfl z V _ _ rfl (by omega), hz, ev_zero]
    rw [hz0, map_zero, smul_zero, add_zero, map_res]
  · rw [ev_δ_succ hww _ V k (-((k + 1 : ℕ) : ℤ) + w) t rfl ht y, cval_ev]
    obtain rfl : t = -((k + 1 : ℕ) : ℤ) + w + 1 := by omega
    have e2 : ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) (cval μ z hw a) k (-((k + 1 : ℕ) : ℤ) + w + 1) (by omega) V (y.face i) =
        ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • μ.mul V m (-(k : ℤ) + n) (-((k + 1 : ℕ) : ℤ) + w + 1) (by omega)
          (Sec.res (fstH y) a) (ev (R := R) z k (-(k : ℤ) + n) rfl V ((Sx.map prod.snd y).face i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cval_ev]
      unfold pval
      rw [fstH_face, map_face]
    rw [e2, cval_ev]
    unfold pval
    rw [μ.leibniz, mul_d_congr μ (t2 := -(k : ℤ) + n) (by push_cast; omega) _ (by push_cast; omega)]
    have hzS := ev_δ_succ (n := n) (m := n + 1) rfl z V k (-((k + 1 : ℕ) : ℤ) + n) (-(k : ℤ) + n) rfl (by push_cast; omega)
      (Sx.map prod.snd y)
    rw [hz, ev_zero, Int.negOnePow_succ, Int.negOnePow_even n hn, Units.neg_smul, one_smul, eq_comm,
      add_neg_eq_zero] at hzS
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hzS, map_sum, ← map_res]
    have hs : w'.negOnePow = -m.negOnePow := by
      rw [← hw', Int.negOnePow_add, Int.negOnePow_succ, Int.negOnePow_even n hn, mul_one]
    simp only [map_zsmul]
    rw [hs, Units.neg_smul]
    exact add_neg_cancel_right _ _

theorem psiC_δ (hn : Even n) (hz : δ n (n + 1) z = 0) : δ n (n + 1) (psiC μ z) = 0 := by
  refine Cochain.ext _ _ fun p q' hpq => ?_
  obtain ⟨w, rfl⟩ : ∃ w, q' = w + 1 := ⟨q' - 1, by omega⟩
  rw [δ_v n (n + 1) rfl _ p (w + 1) hpq w (p + 1) (by omega) rfl, psiC_v, psiC_v, Jcx_d, Int.negOnePow_succ,
    Int.negOnePow_even n hn, Cochain.zero_v, Units.neg_smul, one_smul, add_neg_eq_zero]
  apply Sheaf.hom_ext
  change pmor μ z _ ≫ toSheafify _ _ ≫ sheafifyMap _ (cotD R q N K w) =
    (I₁.d p (p + 1)).hom ≫ pmor μ z _ ≫ toSheafify _ _
  rw [← toSheafify_naturality, ← Category.assoc, ← Category.assoc]
  congr 1
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact cval_δ μ z hn hz _ _ a

end GlobalTheory.EtC.PsiModel

namespace GlobalTheory.EtC.PsiModel

theorem psi_exists : ∀ (q N : ℕ) (i₁ i₂ i : ℤ) (h : i₁ + i₂ = i) (d : ℕ) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) (2 * (d : ℤ))), ∃ ψ : Cocycle (res (ZMod q) (tw q i₁)) (Jcx (ZMod q) q N (res (ZMod q) (tw q i))) (2 * (d : ℤ)), ∀ (m w : ℤ) (hw : m + 2 * (d : ℤ) = w) (U : Scheme.{0}) (a : Sec ((res (ZMod q) (tw q i₁)).X m) U), ∃ c : Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) (res (ZMod q) (tw q i)) w, Sec.map (ψ.1.v m w hw) a = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + w = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev (R := ZMod q) c k s hs V y = twCast h ((twPair q i₁ i₂).mul V m (-(k : ℤ) + 2 * (d : ℤ)) s (by omega) (Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U) a) (ev (R := ZMod q) z.1 k (-(k : ℤ) + 2 * (d : ℤ)) rfl V (Sx.map prod.snd y))) := by
  intro q N i₁ i₂ i h d z
  subst h
  refine ⟨Cocycle.mk (psiC (twPair q i₁ i₂) z.1) (2 * (d : ℤ) + 1) rfl
    (psiC_δ _ _ (even_two_mul _) (z.δ_eq_zero _)), fun m w hw U a => ⟨cval (twPair q i₁ i₂) z.1 hw a, ?_, fun k s hs V y => ?_⟩⟩
  · change Sec.map ((psiC (twPair q i₁ i₂) z.1).v m w hw) a = _
    rw [psiC_v]
    rfl
  · rw [cval_ev]
    rfl

end GlobalTheory.EtC.PsiModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnits
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic

def liftSec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec C U :=
  Function.surjInv (hb U (hE U ⟨x.face 0⟩)).2 (unitSec (lineUnit L x))

theorem liftSec_spec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec.map qb (liftSec qb L hE hb U x) = unitSec (lineUnit L x) :=
  Function.surjInv_eq _ _

theorem liftSec_res {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    Sec.res g (liftSec qb L hE hb U x) = liftSec qb L hE hb V (x.res g) := by
  apply (hb V (hE V ⟨(x.res g).face 0⟩)).1
  rw [← CupSpec.map_res, liftSec_spec, liftSec_spec, PicSpec.unitSec_res, PicSpec.lineUnit_res]

theorem liftSec_face {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 2 U) :
    liftSec qb L hE hb U (x.face 1) = liftSec qb L hE hb U (x.face 0) + liftSec qb L hE hb U (x.face 2) := by
  apply (hb U (hE U ⟨(x.face 0).face 0⟩)).1
  rw [PicSpec.sec_map_add, liftSec_spec, liftSec_spec, liftSec_spec, PicSpec.lineUnit_face, PicSpec.unitSec_mul]

def liftFam {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((sgl C).X s) U
  | 1, s, h, U, x => Sec.map ((sgl C).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (sglι C) (liftSec qb L hE hb U x))
  | _, _, _, _, _ => 0

theorem liftFam_nat {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (liftFam qb L hE hb p s h U x) = liftFam qb L hE hb p s h V (x.res g) := by
  match p with
  | 0 => exact map_zero _
  | 1 =>
    simp only [liftFam]
    rw [CupSpec.map_res, CupSpec.map_res, liftSec_res]
  | p + 2 => exact map_zero _

end GlobalTheory.EtC.KumPic

namespace GlobalTheory.EtC.KumPic

theorem liftFam_one {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E 1 U) :
    liftFam qb L hE hb 1 0 h U x = Sec.map (sglι C) (liftSec qb L hE hb U x) := by
  simp [liftFam, Sec.map]

theorem liftFam_cocycle {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (α : Cochain ((chains ℤ).obj E) (sgl C) 1)
    (hα : ∀ p s h U x, ev α p s h U x = liftFam qb L hE hb p s h U x) : δ 1 2 α = 0 := by
  apply CupSpec.ev_ext
  intro p t ht U x
  rw [CupSpec.ev_zero]
  by_cases h0 : t = 0
  · subst h0
    obtain rfl : p = 2 := by omega
    rw [CupSpec.ev_δ_succ (by norm_num) α U 1 (-1) 0 (by simp) ht x]
    simp only [hα]
    rw [show liftFam qb L hE hb 2 (-1) (by simp) U x = 0 from rfl, PicSpec.sec_map_zero, zero_add, Fin.sum_univ_three]
    simp only [liftFam_one]
    rw [liftSec_face, PicSpec.sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  · exact PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h0) _

theorem lift_cocycle : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  intro q C qb E L hE hb
  obtain ⟨α, hα⟩ := CupSpec.ev_exists (liftFam qb L hE hb) (liftFam_nat qb L hE hb)
  refine ⟨Cocycle.mk α 2 (by norm_num) (liftFam_cocycle qb L hE hb α hα), fun U x => ⟨liftSec qb L hE hb U x,
    liftSec_spec qb L hE hb U x, ?_⟩⟩
  refine (hα 1 0 _ U x).trans ?_
  exact liftFam_one qb L hE hb _ U x

end GlobalTheory.EtC.KumPic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCofilteredLimitAffineEtaleOfIsStalkStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → ∃ (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I) (G : I ⥤ Over S) (π : (Functor.const I).obj (Over.mk s) ⟶ G), Nonempty (IsLimit (Cone.mk _ π)) ∧ ∀ i, IsAffine (G.obj i).left ∧ Etale (G.obj i).hom := by
  first | (exact @GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk) | (exact GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk) | (intros; apply GlobalTheory.EtC.exists_cofiltered_limit_affine_etale_of_isStalk  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleStageDivisorStrictHenselisationOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (b₁ c₁ : Localization.AtPrime Q),
        b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s ∧ j b₁ = b ∧ j c₁ = c := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_divisor) | (exact GlobalTheory.KeyOriginCut.exists_stage_divisor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_divisor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J), (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧ ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n), ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β := by
  first | (exact @GlobalTheory.EtC.SemiMap.op_image_spec) | (exact GlobalTheory.EtC.SemiMap.op_image_spec) | (intros; apply GlobalTheory.EtC.SemiMap.op_image_spec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseUnipotentVolumeConjDiagonalEqStatement
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverseUnipotentVolume_conj_diagonal_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (ϖ : kˣ), IsUnif ϖ → ∀ t : n ⊕ Fin c, ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) = (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by
  first | exact @GlobalTheory.DiagVol.invVol_diag_one | exact GlobalTheory.DiagVol.invVol_diag_one | (intros; apply GlobalTheory.DiagVol.invVol_diag_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariantStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mulP_eq_of_transl_invariant : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (a : G.A (n + 1)), G.transl n a = a ⊗ₜ[R] 1 → ∃ e : G.A n, G.mulP n e = a := by
  first | exact @GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | exact GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | (intros; apply GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq <;> assumption)
end

