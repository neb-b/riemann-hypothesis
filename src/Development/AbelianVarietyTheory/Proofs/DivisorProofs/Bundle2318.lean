module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.Mum.TensTor

section Values

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def GtRelV (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (v' : N'.Gt) (vs : Fin r → N.Gt) : Prop :=
  (∀ j, φ v'.b j = (vs j).b) ∧ ∀ χ' : N'.X,
    (v'.s χ' : F) * wv (N'.c χ') * wv v'.b =
      ((∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
          (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
            N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j : Fˣ) : F) *
        wv (N'.c χ' * v'.b) * wv 1

def QRelV (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) {k : ℕ}
    (q' : N'.QT k) (qs : Fin r → N.QT k) : Prop :=
  (∀ i, e q'.1.1.toAdd i = (qs i).1.1.toAdd) ∧ GtRelV W φ e wv q'.1.2 (fun j => (qs j).1.2)

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def cmp (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) (j : Fin r) : N.A :=
  ν.eA.symm (ν'.eA x ≫ T.pr j)

def chi (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ : N'.X) (i : Fin r) : N.X :=
  ν.eX.symm (T.xe (ν'.eX χ) i)

def wv (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) : F :=
  valF (ν'.eA x).left _
    (T.w.s (fun k => ν.J ((ν'.eA x).left ≫ tensφ T.pr k), ν'.J (ν'.eA x).left)).val

def GtRel (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (v' : N'.Gt) (vs : Fin r → N.Gt) : Prop :=
  GtRelV W (cmp T ν ν') (chi T ν ν') (wv T ν ν') v' vs

def PtRel (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') {k : ℕ} (p' : QkPt D' F k)
    (ps : Fin r → QkPt D F k) : Prop :=
  ∃ (q' : N'.QT k) (qs : Fin r → N.QT k), ν'.QPt p' q' ∧ (∀ i, ν.QPt (ps i) (qs i)) ∧
    QRelV W (cmp T ν ν') (chi T ν ν') (wv T ν ν') q' qs

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

section Facts

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def TensFacts (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) :
    Prop :=
  (∀ x y j, φ (x * y) j = φ x j * φ y j) ∧ Function.Bijective φ ∧
  (∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) ∧ Function.Bijective e ∧
  (∀ χ' j, φ (N'.c χ') j = N.c (e χ' j)) ∧ (∀ x, wv x ≠ 0) ∧
  (∀ x y u, (N'.θ x y u : F) * wv (x * y * u) * wv x * wv y * wv u =
    ((∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j : Fˣ) : F) *
      wv (x * y) * wv (x * u) * wv (y * u) * wv 1) ∧
  ∀ χ', (N'.ψ χ' : F) * wv 1 = wv (N'.c χ') * ((∏ i, ∏ j, N.τ (e χ' i) (e χ' j) ^ W i j : Fˣ) : F)

end Facts

end GlobalTheory.Mum.TensTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLiftMulByNatConvPowerComulEqSucc
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem tensorLift_mulByNatConvPower_comul_eq_succ {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] (i : ℕ) (a : D) :
    (Algebra.TensorProduct.lift (mulBy R D i : D →ₐ[R] D) (AlgHom.id R D) fun _ _ ↦ Commute.all _ _)
      (Coalgebra.comul a) = mulBy R D (i + 1) a := by
  have h1 := comp_mulBy_pts (AlgHom.id R D) i
  have h2 := comp_mulBy_pts (AlgHom.id R D) (i + 1)
  rw [AlgHom.id_comp] at h1 h2
  have h3 : mulBy R D (i + 1) a = (toConv (AlgHom.id R D) ^ (i + 1)).ofConv a := DFunLike.congr_fun h2 a
  rw [h3, pow_succ]
  have h4 := AlgHom.convMul_apply (toConv (AlgHom.id R D) ^ i) (toConv (AlgHom.id R D)) a
  refine Eq.trans ?_ h4.symm
  rw [← h1]

theorem diagSum_cobOne_eq {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] (m : ℕ) (a : D) :
    diagSum R D m (cobOne R D a) = mulBy R D m a - algebraMap R D (Coalgebra.counit a) - m • a := by
  induction m with
  | zero =>
    have h := DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id R D) 0) a
    rw [AlgHom.id_comp, pow_zero] at h
    have h' : mulBy R D 0 a = algebraMap R D (Coalgebra.counit a) := h
    simp [diagSum, h']
  | succ m ih =>
    have e : diagSum R D (m + 1) (cobOne R D a) = diagSum R D m (cobOne R D a) +
        (Algebra.TensorProduct.lift (mulBy R D m : D →ₐ[R] D) (AlgHom.id R D) fun _ _ ↦ Commute.all _ _)
          (cobOne R D a) := by
      simp [diagSum, Finset.sum_range_succ, LinearMap.add_apply]
    rw [e, ih, cobOne_apply, map_sub, map_sub, tensorLift_mulByNatConvPower_comul_eq_succ, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul, map_one, map_one, _root_.mul_one, _root_.one_mul, AlgHom.id_apply, succ_nsmul]
    have hc : ((mulBy R D m : D →ₐ[R] D) a) = mulBy R D m a := rfl
    rw [hc]
    abel

end GlobalTheory.PtExt

theorem GlobalTheory.PtExt.diagSum_cobOne_eq_zero : ∀ (p : ℕ)  (R : Type) [CommRing R] (G : PDivGroup p R) (N : ℕ), (p : R) ^ N = 0 → ∀ a : G.A N, diagSum R (G.A N) (p ^ N) (cobOne R (G.A N) a) = 0 := by
  intro p R _ G N hN a
  rw [GlobalTheory.PtExt.diagSum_cobOne_eq, G.mulBy_pow_self N a, sub_self, zero_sub, neg_eq_zero,
    ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, hN, zero_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBack
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensCub

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR

section Box

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {pr : K₀ → (X' ⟶ X)} {εp : K₀ → ℤ}

def bwg {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr εp)) (ψ : Z ⟶ X') (z : Z) (jN : K₀ → M.ι) (k : M'.ι) :
    (Z.presheaf.stalk z)ˣ := gm ψ z (LB.wchart M pr jN ⊓ M'.U k) (w.s (jN, k))

theorem bwg_trans {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr εp)) (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : K₀ → M.ι} {k k' : M'.ι} (h₁ : ψ z ∈ LB.wchart M pr jN) (h₁' : ψ z ∈ LB.wchart M pr jN')
    (h₂ : ψ z ∈ M'.U k) (h₂' : ψ z ∈ M'.U k') :
    bwg w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i)) ^ εp i) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bwg w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  have d := gm_div M' (LB.LinComb M pr εp) ψ z (jN, k) (jN', k') hm
  have l := gm_linComb M pr εp ψ z jN jN' h₁ h₁'
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res ψ z _ hm _))))

theorem gm_linCombIsoG {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr εp)) {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (jN : K → K₀ → M.ι) (jM : K → M'.ι)
    (hz : r z ∈ LB.wchart (LB.LinComb M pr εp) φ jN ⊓ LB.wchart M' φ jM) :
    gm r z (LB.wchart (LB.LinComb M pr εp) φ jN ⊓ LB.wchart M' φ jM) ((LB.linCombIso w φ ε).s (jN, jM)) =
      ∏ a, bwg w (r ≫ φ a) z (jN a) (jM a) ^ ε a :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a)
    ((gm_res r z _ hz _).trans (gm_pull r (φ a) z (LB.wchart M pr (jN a) ⊓ M'.U (jM a))
      ⟨Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a⟩ _))))

variable {K : Type} [Fintype K]

def ratio (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (ρ : K₀ → (Y ⟶ Y₀)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jN : K → K₀ → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bwg w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) ^ εp i)⁻¹

theorem chart_le {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ρ : K₀ → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a) (jN : K → K₀ → M.ι) (i : K₀) :
    LB.wchart (LB.LinComb M pr εp) φ' jN ≤ ρ i ⁻¹ᵁ LB.wchart M φ (fun a => jN a i) := fun y hy =>
  Set.mem_iInter.2 fun a => (congrArg (fun g : Y ⟶ X => g y ∈ M.U (jN a i)) (hψ i a)).mp
    (Set.mem_iInter.1 (Set.mem_iInter.1 hy a) i)

end Box

end GlobalTheory.TensCub

namespace GlobalTheory.TensCub
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR
section Box2
variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {pr : K₀ → (X' ⟶ X)} {εp : K₀ → ℤ}
variable {K : Type} [Fintype K]

theorem ratio_trans (w : LB.Iso M' (LB.LinComb M pr εp)) (hw : w.IsGen) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : K₀ → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {jN jN' : K → K₀ → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)
    (h' : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN' ⊓ LB.wchart M' φ' jM') :
    ratio w ρ t' t r z jN jM = ratio w ρ t' t r z jN' jM' := by
  have e₁ : ∀ a, bwg w (r ≫ φ' a) z (jN a) (jM a) = _ := fun a => bwg_trans w hw (r ≫ φ' a) z (jN' := jN' a) (k' := jM' a)
    (Set.mem_iInter.1 h.1 a) (Set.mem_iInter.1 h'.1 a) (Set.mem_iInter.1 h.2 a) (Set.mem_iInter.1 h'.2 a)
  have e₂ := gen_trans ht' r z h.2 h'.2
  have e₃ : ∀ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) = _ := fun i =>
    gen_trans ht (r ≫ ρ i) z (j' := fun a => jN' a i) (chart_le hψ jN i h.1) (chart_le hψ jN' i h'.1)
  have e₄ : ∏ i, trF (L := M) φ ε (r ≫ ρ i) z (fun a => jN a i) (fun a => jN' a i) ^ εp i =
      ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (jN a i) ⊓ M.U (jN' a i)) (M.g (jN a i) (jN' a i)) ^ εp i) ^ ε a := by
    unfold trF
    simp_rw [← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, ← zpow_mul, mul_comm, Category.assoc, Category.assoc, hψ]
  unfold ratio
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂,
    Finset.prod_congr rfl fun i _ => congrArg (· ^ εp i) (e₃ i)]
  simp only [mul_zpow, Finset.prod_mul_distrib, e₄]
  simp only [inv_zpow, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : K₀ → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε)) (jN : K → K₀ → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
        r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM →
        gm r z _ u = ratio w ρ t' t r z jN jM := by
  refine ⟨@id (Γ(Y, LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
      ((LB.linCombIso w φ' ε).s (jN, jM)) * res inf_le_right (t'.s jM) *
      (∏ i, res (inf_le_left.trans (chart_le hψ jN i)) (pullU (ρ i) _ (t.s (fun a => jN a i))) ^ εp i)⁻¹,
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linCombIsoG w φ' ε r z jN jM hz) (gm_res r z _ hz _))) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ εp i) ?_))))))
  exact (gm_res r z _ hz _).trans (gm_pull r (ρ i) z _ (chart_le hψ jN i hz.1) _)

theorem box_unique {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr εp))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : K₀ → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bwg w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ i, val t (e ≫ ρ i) y J ^ εp i)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bwg w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ i, val t (r ≫ ρ i) z J ^ εp i := by
  choose u hu using fun q : (K → K₀ → M.ι) × (K → M'.ι) => exists_ratio w hψ t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens)
    (fun q : (K → K₀ → M.ι) × (K → M'.ι) =>
      LB.wchart (LB.LinComb M pr εp) φ' q.1 ⊓ LB.wchart M' φ' q.2) (fun _ => le_top)
    (fun y _ => by
      choose a ha using fun k i => exists_chart hM (pr i (φ' k y))
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(a, b), Set.mem_iInter.2 fun k => Set.mem_iInter.2 (ha k), Set.mem_iInter.2 hb⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratio_trans w hw hψ ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bwg w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ i, val t (r ≫ ρ i) z J ^ εp i)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
      ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩
    have v : ∏ i, val t (r ≫ ρ i) z J ^ εp i = ∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => J ((r ≫ φ' a) ≫ pr i)))
        (t.s (fun a => J ((r ≫ φ' a) ≫ pr i))) ^ εp i := Finset.prod_congr rfl fun i _ =>
      congrArg (· ^ εp i) (val_of t _ z J _ (fun a => by rw [Category.assoc, Category.assoc, hψ]))
    rw [v]
    have w₁ := (hu (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Box2
end GlobalTheory.TensCub

namespace GlobalTheory.TensCub

def tensP {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} (T : Tens D D' W)
    (k : (Fin r × Fin r) × Fin 4) : D'.P.A ⟶ D.P.A :=
  ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2

theorem tensorMap_left {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : (tensP T k).left = tensφ T.pr k := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m <;> rfl

theorem isMonHom_tensorMap {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : IsMonHom (tensP T k) := by
  letI := D.P.isAb.comm
  have := T.pr_hom k.1.1
  have := T.pr_hom k.1.2
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m
  · exact GlobalTheory.Serre.isMonHom_mul _ _
  · exact T.pr_hom i
  · exact T.pr_hom j
  · exact GlobalTheory.Serre.isMonHom_one

theorem cubV_tens : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (S : Over (Spec (CommRingCat.of R))) (z : S.left) (J : (S.left ⟶ D.P.A.left) → D.P.L.ι) (J' : (S.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ x x' y : S ⟶ D'.P.A, (let om := fun p : S ⟶ D'.P.A => gm p.left z _ (T.w.s (fun k => J (p.left ≫ tensφ T.pr k), J' p.left)); cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ k : (Fin r × Fin r) × Fin 4, cubV D.cub z J (x ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (x' ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (y ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) ^ tensε W k) := by
  intro hG R _ _ D D' r W T S z J J' hJ hJ' x x' y om
  let P := tensP T
  let ρ : (Fin r × Fin r) × Fin 4 → ((G3 D'.P.A).left ⟶ (G3 D.P.A).left) := fun k => (P k ⊗ₘ P k ⊗ₘ P k).left
  have hψ : ∀ k a, thφ D'.P.A (x3 D'.P.A) a ≫ tensφ T.pr k = ρ k ≫ thφ D.P.A (x3 D.P.A) a := fun k a => by
    rw [← tensorMap_left T k]
    letI := isMonHom_tensorMap T k
    exact (CubeMap.ofHom (P k)).psum_comm a.down
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (a b c : T ⟶ D'.P.A) k, (lift a (lift b c)).left ≫ ρ k =
      (lift (a ≫ P k) (lift (b ≫ P k) (c ≫ P k))).left := fun a b c k => by
    show (lift a (lift b c) ≫ (P k ⊗ₘ P k ⊗ₘ P k)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := tensφ T.pr) (εp := tensε W) D.P.isLB D'.P.isLB T.w T.w_gen (ε := thε) hψ
    D'.cub.isGen D.cub.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV D'.cub s I') := isCub_cubV D'.cub hI'
      have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I) := isCub_cubV D.cub hI
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
        (fun q => bwg T.w q s (fun i => I (q ≫ tensφ T.pr i)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      have := isMonHom_tensorMap T k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ P k = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ k = _ from hρ 1 1 1 k, o]
      exact (congrArg (· ^ tensε W k) (C.face 1 1)).trans (one_zpow _)) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bwg T.w q z (fun i => J (q ≫ tensφ T.pr i)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun k _ => ?_)))
  rw [hρ]; rfl

end GlobalTheory.TensCub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSurjectiveKerOfAffinePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem tensor_of_pullback_surj_ker : ∀ {R O R' Q : Type} [CommRing R] [CommRing O] [CommRing R'] [CommRing Q] [Algebra R O] [Algebra R R'] [Algebra R Q] (I : Ideal R') (a : O →ₐ[R] Q) (b : R' ⧸ I →ₐ[R] Q), IsPullback (spMap (a : O →+* Q)) (spMap (b : R' ⧸ I →+* Q)) (spMap (algebraMap R O)) (spMap (algebraMap R (R' ⧸ I))) → Function.Surjective (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) = I.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') := by
  intro R O R' Q _ _ _ _ _ _ _ I a b hP
  set t : TensorProduct R O (R' ⧸ I) →ₐ[R] Q := Algebra.TensorProduct.lift a b fun _ _ => Commute.all _ _ with ht
  have H0 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R O (R' ⧸ I))
  have e1 : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) ≫
      Spec.map (CommRingCat.ofHom (S := TensorProduct R O (R' ⧸ I)) Algebra.TensorProduct.includeLeftRingHom) =
      spMap (a : O →+* Q) := by
    rw [← Spec.map_comp]; congr 1; ext x; simp [ht]
  have e2 : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) ≫
      Spec.map (CommRingCat.ofHom (S := TensorProduct R O (R' ⧸ I)) Algebra.TensorProduct.includeRight.toRingHom) =
      spMap (b : R' ⧸ I →+* Q) := by
    rw [← Spec.map_comp]; congr 1; ext x; simp [ht]
  have hiso : IsIso (Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q))) := by
    have : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) = (hP.isoIsPullback _ _ H0).hom := by
      apply H0.hom_ext
      · rw [e1, IsPullback.isoIsPullback_hom_fst]
      · rw [e2, IsPullback.isoIsPullback_hom_snd]
    rw [this]; infer_instance
  rw [isIso_SpecMap_iff] at hiso
  have hbij : Function.Bijective t := hiso
  have hcomp : (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) =
      t.comp (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [ht]
  have hmk : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I
  rw [hcomp]
  refine ⟨hbij.2.comp (LinearMap.lTensor_surjective O hmk), ?_⟩
  have : RingHom.ker (t.comp (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I))) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I)) := by
    ext x
    simp only [RingHom.mem_ker, AlgHom.comp_apply]
    constructor
    · intro h; exact hbij.1 (by rw [h, map_zero])
    · intro h; rw [h, map_zero]
  rw [this, Algebra.TensorProduct.lTensor_ker _ hmk]
  congr 1
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.MBLow.TRank

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  intro K _ _ _ x g hg m hm hm3 I pt hpt ϑ J hTJ c₀ c hrel
  obtain ⟨th, hth, U, t, i₀, c', hUt, hi₀, hval⟩ := hTJ
  have hg1 : 1 ≤ g := hg ▸ x.g_pos
  let j₀ : Fin g := ⟨0, hg1⟩
  have hy : ∀ j : Fin g, epsLift (x.v (j.cast hg.symm)) ≫ (fst (baseOver (Sp K)) x.P.A).left =
      spMap (algebraMap K (DualNumber K)) := fun j => by
    rw [epsLift, ← Over.comp_left, lift_fst]; rfl
  choose f hf using fun j : Fin g => _root_.GlobalTheory.SecValLin.exists_linear_valR_sec K x (m ^ 2) (fun _ => i₀) (DualNumber K) _ (hy j)
  set a := c₀ - ∑ j, c j * c' j with ha
  let Φ : EA x.P (𝟙 (Sp K)) (m ^ 2) →ₗ[K] K :=
    a • ((TrivSqZeroExt.fstHom K K K).toLinearMap ∘ₗ f j₀) + ∑ j, c j • (TrivSqZeroExt.sndHom K K ∘ₗ f j)
  have hΦ : ∀ s, Φ s = a * (f j₀ s).fst + ∑ j, c j * (f j s).snd := fun s => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    rfl
  have hft : ∀ j i, f j (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) =
      valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K))).U fun _ => i₀)
        ((t i).f fun _ => i₀) := fun j i => hf j _
  have hΦt : ∀ i, Φ (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) = 0 := fun i => by
    rw [hΦ]
    simp only [hft, hval]
    set r := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val ^ (m ^ 2)
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add, mul_zero, zero_mul]
    have e1 : ∑ j, c j * (r * (J i j + c' j * ϑ i)) = r * ∑ j, c j * J i j + r * ϑ i * ∑ j, c j * c' j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ha]
    linear_combination r * hrel i
  have hspan := _root_.GlobalTheory.TSpan.span_eq_top K x m hm hm3 I pt hpt th hth U t hUt
  have hΦ0 : Φ = 0 := LinearMap.ext_on_range hspan fun i => by rw [hΦt i, LinearMap.zero_apply]
  have hsep := _root_.GlobalTheory.MBLow.JetSep.sep K x g hg (m ^ 2) (by nlinarith) i₀ hi₀ j₀ a c fun s => by
    have h := congrArg (fun F => F (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left s)) hΦ0
    simp only [LinearMap.zero_apply, hΦ] at h
    rw [hf j₀, Finset.sum_congr rfl fun j _ => by rw [hf j]] at h
    exact h
  obtain ⟨h1, h2⟩ := hsep
  refine ⟨?_, h2⟩
  subst h2
  simpa [ha] using h1

end GlobalTheory.MBLow.TRank
end
end

