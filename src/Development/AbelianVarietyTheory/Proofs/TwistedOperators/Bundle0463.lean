module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateLast
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastRowMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem negGA_mem_fin (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem fockComp_mul_right (B : VertexFrames G) (i : ℕ) (hi : (Pair.chi i D.R.m : Pair T).InRange D.R.m)
    {f : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (a : FinPt G (.grid i D.R.m)) (b h : FinPt G (.grid (i + 1) D.R.m)) :
    fockComp W B (.chi i D.R.m : Pair T) f a (b * h) =
      fockComp W B (.chi i D.R.m : Pair T) (W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m : Pair T) 1 h.1) f) a b := by
  unfold fockComp
  congr 1
  funext k
  unfold jetTab kerFin GridData.Weil.ker thetaKO
  have e1 : G.toPair (.chi i D.R.m : Pair T) (a : GA D (G.V (Pair.chi i D.R.m : Pair T).small))
      ((b * h : FinPt G (.grid (i + 1) D.R.m)) : GA D _) =
      G.toPair (.chi i D.R.m : Pair T) a b * G.toPair (.chi i D.R.m : Pair T) 1 h.1 := by
    simp [GridData.toPair, Prod.ext_iff, map_mul]
  have e2 : G.toPair (.chi i D.R.m : Pair T) 1 h.1 = (negGA _ h.1, (1 : GA D _)) := rfl
  rw [e1, map_mul, Module.End.mul_apply, e2]
  unfold fockIn
  rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om _) (W.om_is _ hi) W.θ W.θ_is (negGA _ h.1) (negGA_mem_fin _ h.2)
    1 (one_mem _) _ _ _ _ f _ hf]

theorem update_grid_eq {a b : ℕ} (h : a = b) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : FinPt G (.grid a D.R.m)) :
    Function.update y a v b = h ▸ v := by
  subst h; simp

theorem cast_mul_grid {a b : ℕ} (h : a = b) (y : ∀ i, FinPt G (.grid i D.R.m)) (p : FinPt G (.grid a D.R.m)) :
    (h ▸ (y a * p) : FinPt G (.grid b D.R.m)) = y b * (h ▸ p : FinPt G (.grid b D.R.m)) := by
  subst h; rfl

theorem cast_conj_grid {a b : ℕ} (h : a = b) (u : ∀ X : Node, FinPt G X) (p : FinPt G (.grid a D.R.m)) :
    (h ▸ ((u (.grid a D.R.m))⁻¹ * p * u (.grid a D.R.m)) : FinPt G (.grid b D.R.m)) =
      (u (.grid b D.R.m))⁻¹ * (h ▸ p : FinPt G (.grid b D.R.m)) * u (.grid b D.R.m) := by
  subst h; rfl

end GlobalTheory.LastRowMove

namespace GlobalTheory.LastRowMove

theorem rowMapV_update_last : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
    IsThetaFunO W.ψ (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) (gs (lastIx D)) →
    rowMapV S gs (Function.update y D.R.m (y D.R.m * k)) = rowMapV S (Function.update gs (lastIx D) (rowShift S k (gs (lastIx D)))) y := by
  intro D T L sc G W U S gs y k hf
  unfold rowMapV
  refine congrArg (fun q => LinearMap.comp (chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m))) q D.R.m) _) ?_
  funext j
  by_cases hjm : j < D.R.m
  · rw [dite_eq_left hjm, dite_eq_left hjm]
    by_cases hj1 : j + 1 < D.R.m
    · have h1 : j ≠ D.R.m := by omega
      have h2 : j + 1 ≠ D.R.m := by omega
      have h3 : (⟨j, hjm⟩ : Fin D.R.m) ≠ lastIx D := by
        intro h; have := congrArg Fin.val h; simp [lastIx] at this; omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · obtain rfl : j = (lastIx D : ℕ) := by simp [lastIx]; omega
      have h1 : ((lastIx D : ℕ)) ≠ D.R.m := by have := lastIx_succ D; omega
      rw [Function.update_of_ne h1, update_grid_eq (lastIx_succ D), cast_mul_grid (lastIx_succ D)]
      have e : ∀ a p v : FinPt G (.grid ((lastIx D : ℕ) + 1) D.R.m), a * p * v = a * v * (v⁻¹ * p * v) := by
        intro a p v; group
      rw [e, ← cast_conj_grid (lastIx_succ D) S.N.u]
      have hf' : IsThetaFunO W.ψ _ _ (gs ⟨(lastIx D : ℕ), hjm⟩) := hf
      rw [fockComp_mul_right _ _ (inRange_chi (lastIx D)) hf',
        show Function.update gs (lastIx D) (rowShift S k (gs (lastIx D))) ⟨(lastIx D : ℕ), hjm⟩ =
          rowShift S k (gs (lastIx D)) from Function.update_self _ _ _]
      rfl
  · rw [dite_eq_right hjm, dite_eq_right hjm]

end GlobalTheory.LastRowMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledTensorLatticeLeCompletedHomLatticeOffPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel.TrOff

section Help
variable {D : D7} {S T : HSp D}

theorem partAt_add (c : AE D) (x y : WO S T) :
    GlobalTheory.LiftLevel.partAt c (x + y) = GlobalTheory.LiftLevel.partAt c x + GlobalTheory.LiftLevel.partAt c y :=
  Matrix.ext fun i j => mul_add c (x i j) (y i j)

theorem partAt_zero (c : AE D) : GlobalTheory.LiftLevel.partAt c (0 : WO S T) = 0 :=
  Matrix.ext fun _ _ => mul_zero c

theorem partAt_neg (c : AE D) (x : WO S T) : GlobalTheory.LiftLevel.partAt c (-x) = -GlobalTheory.LiftLevel.partAt c x :=
  Matrix.ext fun i j => mul_neg c (x i j)

noncomputable def gm (S T : HSp D) (γ : Af D.host.F) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : WO S T :=
  Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a

theorem gm_add (γ : Af D.host.F) (x y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    gm S T γ (x + y) = gm S T γ x + gm S T γ y :=
  Matrix.ext fun a k => TensorProduct.tmul_add _ (x k a) (y k a)

theorem gm_zero (γ : Af D.host.F) : gm S T γ 0 = 0 :=
  Matrix.ext fun a k => TensorProduct.tmul_zero _ _

theorem gm_neg (γ : Af D.host.F) (x : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    gm S T γ (-x) = -gm S T γ x :=
  Matrix.ext fun a k => TensorProduct.tmul_neg _ (x k a)

theorem partAt_gm (σ α : Af D.host.F) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    GlobalTheory.LiftLevel.partAt (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) (gm S T α y) =
      gm S T ((1 - σ) * α) y := by
  refine Matrix.ext fun a k => ?_
  change (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a) =
    (pairA D.host.F 0 ((1 - σ) * α)) ⊗ₜ[D.host.F] y k a
  rw [sub_mul, one_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← TensorProduct.sub_tmul]
  congr 1
  refine Prod.ext ?_ ?_
  · change (0 : Ainf D.host.F) - _ * 0 = 0
    rw [mul_zero, sub_zero]
  · change α - σ * α = (1 - σ) * α
    ring

end Help

theorem mem_stdL_int {E : Type} [Field E] [NumberField E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdL E n ↔ ∀ a, IsIntegral ℤ (v a) := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      show IsIntegral ℤ ((Pi.single b 1 : Fin n → E) a)
      by_cases h : a = b
      · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
      · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx => intro a; exact (c.2).mul (hx a)
  · intro h
    have e : v = ∑ a, (⟨v a, h a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same]
        change v i = v i * 1
        rw [mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem star_stdL : ∀ (D : D7) (n : ℕ) (v : Fin n → D.host.E), v ∈ stdL D.host.E n ↔ star v ∈ stdL D.host.E n := by
  intro D n v
  rw [mem_stdL_int, mem_stdL_int]
  refine forall_congr' fun a => ?_
  change _ ↔ IsIntegral ℤ (star (v a))
  exact ⟨fun h => h.map (starRingEnd D.host.E).toIntAlgHom, fun h => by
    have := h.map (starRingEnd D.host.E).toIntAlgHom
    rwa [show (starRingEnd D.host.E).toIntAlgHom (star (v a)) = v a from star_star (v a)] at this⟩

theorem rowTriv : ∀ (D : D7) (S T : HSp D) (k₀ : GA D S) (f : AE D), 0 < T.rank → f * f = f → (∀ x : WO S T, IsHalf f x → actO S T k₀ 1 x = x) → ∀ i j, f * (mt S k₀⁻¹ - 1) i j = 0 := by
  intro D S T k₀ f hT hf h i j
  let i₀ : Fin T.rank := ⟨0, hT⟩
  let x : WO S T := Matrix.of fun a b => if a = i₀ ∧ b = i then f else 0
  have hx : IsHalf f x := fun a b => by
    simp only [x, Matrix.of_apply]
    split_ifs
    · exact hf
    · exact mul_zero f
  have h1 := congrFun (congrFun (h x hx) i₀) j
  unfold actO at h1
  rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · simp only [x, Matrix.of_apply, true_and, if_true] at h1
    rw [Matrix.sub_apply, mul_sub, h1, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · intro b _ hb
    simp [x, hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

end GlobalTheory.LiftLevel.TrOff

namespace GlobalTheory.LiftLevel


open GlobalTheory.LiftLevel.TrOff in
theorem partAt_off_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmover hgen hIsMov Lv hLv u hu
  by_cases hT : T.rank = 0
  · have h0 : GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u = 0 := Matrix.ext fun i _ => absurd i.2 (by omega)
    rw [h0]; exact zero_mem _
  have hTpos : 0 < T.rank := Nat.pos_of_ne_zero hT
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := _root_.GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum D _ e he
  have hf : 1 - e - cA D e = 1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by rw [hσ]; ring
  have hgg : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)
      = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by
    rw [hσ]; exact (GlobalTheory.IdemConjSum.idemSum_add_conj_idem _ e he).1
  have hff : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    rw [hf]; linear_combination hgg
  have hrow := rowTriv D S T k₀ (1 - e - cA D e) hTpos hff hmover.2.1
  rw [hf] at hrow
  have hstar : ∀ v, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank := star_stdL D S.rank
  rw [GlobalTheory.Ker.LatTens.latO_eq_hatA D S T C _ _ ΛT C.X.Λ hstar hAA]
  have hO : ∀ (c : 𝓞 D.host.F), ∀ y ∈ tens (stdL D.host.E S.rank) C.X.Λ,
      (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ tens (stdL D.host.E S.rank) C.X.Λ := fun c y hy =>
    GlobalTheory.Ker.HatLat.smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy
  have hgen' : ∀ α ∈ intAf D.host.F, ∀ y ∈ tens Λ' (Lv.sh C.X.Λ),
      gm S T ((1 - σ) * α) y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
    intro α hα y hy
    have hγ : (1 - σ) * α ∈ intAf D.host.F := by
      intro w
      rw [map_mul, map_sub, map_one]
      by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
      · obtain ⟨PP, hPP, rfl⟩ := hw
        rw [hσ1 PP hPP, sub_self, zero_mul]; exact zero_mem _
      · push_neg at hw
        rw [hσ0 w hw, sub_zero, one_mul]; exact hα w
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u', hu', rfl⟩ := hy
      refine _root_.GlobalTheory.HatPoint.mem_hatA_of_div D S T _ hO _ hγ _ fun w => ?_
      by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
      · left
        obtain ⟨PP, hPP, rfl⟩ := hw
        rw [map_mul, map_sub, map_one, hσ1 PP hPP, sub_self, zero_mul]
      · right
        push_neg at hw
        obtain ⟨t₁, ht₁, h1⟩ := _root_.GlobalTheory.Ker.MoverStd.exists_mul_std D S k₀ Λ' σ w (hσ0 w hw) hrow hIsMov v hv
        have hu'' : u' ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) C.X.Λ := by
          have : Lv.sh C.X.Λ = idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ := rfl
          rw [this, hLv] at hu'; exact hu'
        obtain ⟨t₂, ht₂, h2'⟩ := _root_.GlobalTheory.TrOffShift.shift_mult D T.rank Pg Q C.X.Λ w hw u' hu''
        refine ⟨t₁ * t₂, fun hm => (w.isPrime.mem_or_mem hm).elim ht₁ ht₂, ?_⟩
        refine AddSubgroup.subset_closure ⟨_, h1, _, h2', ?_⟩
        refine Matrix.ext fun i j => ?_
        change algebraMap D.host.F D.host.E ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) * (v i * u' j) =
          algebraMap D.host.F D.host.E (t₁ : D.host.F) * v i * (algebraMap D.host.F D.host.E (t₂ : D.host.F) * u' j)
        rw [show ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) = (t₁ : D.host.F) * (t₂ : D.host.F) from rfl, map_mul]
        ring
    | zero => rw [gm_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [gm_add]; exact add_mem hx hy
    | neg x _ hx => rw [gm_neg]; exact neg_mem hx
  rw [hf]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    exact (partAt_gm σ α y).symm ▸ hgen' α hα y hy
  | zero => rw [partAt_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [partAt_add]; exact add_mem hx hy
  | neg x _ hx => rw [partAt_neg]; exact neg_mem hx

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwise
section
open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem schwartz_tendsto_apply_of_tendsto_pointwise :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  intro V _ _ _ S hS g g₀ hg
  haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := schwartzMap_barrelledSpace V
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have hq := schwartz_withSeminorms ℂ V ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ fun n => S (u n)) := by
    refine hq.banach_steinhaus (𝓕 := fun n => S (u n)) ?_
    intro k f
    exact ((hq.continuous_seminorm k).tendsto f).comp ((hS f).comp hu) |>.bddAbove_range
  have hE := hUE.equicontinuous g₀
  have h1 : Tendsto (fun n => (S (u n) g₀, S (u n) (g (u n)))) atTop (𝓤 (SchwartzMap V ℂ)) := by
    intro U hU
    have := (hg.comp hu).eventually (hE U hU)
    rw [Filter.mem_map]
    exact this.mono fun n hn => hn n
  exact ((hS g₀).comp hu).congr_uniformity h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceModelOnto

variable {D : D7}

theorem isSBHalf_zero {m n : ℕ} (a : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf a Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem isSBHalf_smul {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf a Λ Φ) : IsSBHalf a Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (hne t ht), k, hk,
    fun u hu hu' t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hu' t], fun t ht => h3 t (hne t ht)⟩

theorem isSBHalf_add {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf a Λ Φ) (h' : IsSBHalf a Λ Ψ) : IsSBHalf a Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have hne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf a u → IsHalf a (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (hh _ _ hu') t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (hh _ _ hu') t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem placeModel_onto_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (a : AE D), IsSplitIdem D a → a + cA D a = idem D (.inl v) → (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧ ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → (∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ)) ∧ ∀ x, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x := by
  first
  | exact @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | (apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local ..)

end GlobalTheory.PlaceModelOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceChartFramesConjMaximalCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section
namespace GlobalTheory.SplitChartLink

theorem block_frame_conjugation_identity {G H : Type} [Group G] [Group H] (f : G →* H) (a x : G) :
    (f a)⁻¹ * f (a * x * a⁻¹) * f a = 1⁻¹ * f x * 1 := by
  simp only [map_mul, map_inv]
  group

theorem rdA_matHom_embV {D : D7} (T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (g : Gv T v) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) (Formalism.L2.Theta.matHom T (embV T v g)) =
      splitHom D.sp.cm.sig T.gram (GlobalTheory.SplitProjChart.emb φ) g := by
  have h1 : GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram g =
      Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom T (embV T v g)) := by
    have h2 := GlobalTheory.AdelicU.matHom_proj D.sp.cm.sig T.gram v (embV T v g)
    rw [GlobalTheory.AdelicU.proj_emb_self] at h2
    exact h2
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [splitHom_val, h1, GlobalTheory.SplitProjChart.splitProj_emb]
  rfl

theorem link : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∃ φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε ∧ (∃ BS, GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS) ∧ ∃ BT, GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT ∧ ∃ ψ : Fv D.host.F v ≃+* w.adicCompletion D.host.E, (∀ a, Valued.v (ψ a) = Valued.v a) ∧ qV D.host.F v = qV D.host.E w ∧ ∃ κ ∈ KGL v (n := T.rank), ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT (embV T v (e.symm x)) = κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x * κ := by
  intro D S T v w h hv e he ε hε
  obtain ⟨v', φ, hφ, hP⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 ε w hε
  have hv' : v' = v := by
    have := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v' φ w hP).1
    subst h
    exact HeightOneSpectrum.ext this.symm
  subst hv'
  have hE : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  set τ := GlobalTheory.SplitProjChart.emb φ with hτdef
  have hφτ : splitProj τ = φ := GlobalTheory.SplitProjChart.splitProj_emb φ
  have hτ : splitPrime τ = w := ((GlobalTheory.SplitIdemDict.isProjAt_iff τ w).1 (hφτ ▸ hP)).symm
  obtain ⟨hch, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v' φ ε hφ
  have hemb : chartEmb hch = τ := AlgHom.ext fun x => by
    rw [chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  have hfr : ∀ (V : HSp D) β, GlobalTheory.SplitHecke.Frame V ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) β ↔ IsSplitBasis τ (frameLat V) β :=
    fun V β => by rw [GlobalTheory.AdelicU.SplitFrame.frame_iff_isSplitBasis hφ.1 hch, hemb]
  set ψ := ConjPlace.complEquiv hE h hτ with hψ
  obtain ⟨⟨a, ha, hea⟩, -⟩ := he
  have hBT : IsSplitBasis τ (frameLat T) (Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') a) := by
    rw [← ConjPlace.isFrameAt_iff hE h hτ]
    convert ha
    exact Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat S
  obtain ⟨BS, hBS⟩ := exists_isSplitBasis τ (frameLat S) hE
  refine ⟨φ, hφ, ⟨BS, (hfr S BS).2 hBS⟩, _, (hfr T _).2 hBT, ψ, ConjPlace.valued_complMap hE h hτ, ?_, 1, one_mem _, ?_⟩
  · rw [← hτ, GlobalTheory.LFun.SplitTie.qV_splitPrime]
  · intro x
    have h3 := hea (e.symm x)
    rw [MulEquiv.apply_symm_apply, ConjPlace.locMat_eq hE h hτ, ← hψ] at h3
    have h4 : splitHom D.sp.cm.sig T.gram τ (e.symm x) =
        Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') (a * x * a⁻¹) := by
      have h5 : Formalism.UG.bc (ψ : Fv D.host.F v' →+* w.adicCompletion D.host.E) (splitHom D.sp.cm.sig T.gram τ (e.symm x)) =
          a * x * a⁻¹ := by
        generalize Formalism.UG.bc (ψ : Fv D.host.F v' →+* w.adicCompletion D.host.E) (splitHom D.sp.cm.sig T.gram τ (e.symm x)) = y at h3 ⊢
        subst h3
        group
      rw [← h5]
      exact Units.ext (Matrix.ext fun i j => (ψ.symm_apply_apply _).symm)
    have h6 : Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') x =
        Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') x := rfl
    rw [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo, rdA_matHom_embV,
      show splitHom D.sp.cm.sig T.gram (GlobalTheory.SplitProjChart.emb φ) (e.symm x) = _ from h4, ← h6]
    exact block_frame_conjugation_identity _ a x

end GlobalTheory.SplitChartLink
end
end

