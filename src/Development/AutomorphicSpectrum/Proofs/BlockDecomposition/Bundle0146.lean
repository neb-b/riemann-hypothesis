module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0139
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverCupActionBasis
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CechVB

theorem vb_basis : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ V : X.Opens, O →+* Γ(X, V)) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} O) {ι : Type}
    (U : ι → X.Opens) (U' : ι → ObjectProperty C) (m : ℕ) (κ : ι → Type) [∀ α, Fintype (κ α)]
    (act : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Γ(X, capO U i) →+* AddMonoid.End (HU F (capT U' i) m))
    (b : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)), κ (i a) → HU F (capT U' i) m)
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))
    (hfree : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h : HU F (capT U' i) m),
      ∃! f : κ (i a) → Γ(X, capO U i), h = ∑ k, act i (f k) (b i a k))
    (hstr : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (c : O) (h : HU F (capT U' i) m), act i (str _ c) h = c • h)
    (hres : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (f : Γ(X, capO U (i ∘ j.succAbove))) (h : HU F (capT U' (i ∘ j.succAbove)) m),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (act (i ∘ j.succAbove) f h) =
        act i (rs (capO_comp U i j.succAbove) f) ((resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m h))
    (hb : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (a : Fin (n + 1)) (k : κ (i (j.succAbove a))),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (b (i ∘ j.succAbove) a k) = b i (j.succAbove a) k)
    (hg : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a a' : Fin (n + 1)) (k' : κ (i a')),
      b i a' k' = ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i a')) (g (i a) (i a') k k')) (b i a k)),
    Nonempty (VB str U (CrystallineSemistableComparison.Pb.cechH F U' m)) := by
  intro O _ X str C _ F ι U U' m κ _ act b g hfree hstr hres hb hg
  simp only [ExistsUnique] at hfree
  choose co h1 h2 using hfree
  have actadd : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (f f' : Γ(X, capO U i)) (h : HU F (capT U' i) m),
      act i (f + f') h = act i f h + act i f' h := by
    intro n i f f' h
    rw [map_add (f := _)]; rfl
  have actmul : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (f f' : Γ(X, capO U i)) (h : HU F (capT U' i) m),
      act i (f * f') h = act i f (act i f' h) := by
    intro n i f f' h
    rw [map_mul]; rfl
  have actsum : ∀ {n : ℕ} (i : Fin (n + 1) → ι) {κ' : Type} (s : Finset κ') (f : κ' → Γ(X, capO U i))
      (h : HU F (capT U' i) m), act i (∑ k ∈ s, f k) h = ∑ k ∈ s, act i (f k) h := by
    intro n i κ' s f h
    exact map_sum ((AddMonoidHom.eval h).comp (act i).toAddMonoidHom) f s
  have coadd : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h h' : HU F (capT U' i) m),
      co n i a (h + h') = co n i a h + co n i a h' := by
    intro n i a h h'
    refine (h2 n i a _ _ ?_).symm
    conv_lhs => rw [h1 n i a h, h1 n i a h']
    simp only [Pi.add_apply, actadd, Finset.sum_add_distrib]
  refine ⟨{ κ := κ, g := g, e := fun n a =>
              { toFun := fun x i => co n i a (x i)
                invFun := fun f i => ∑ k, act i (f i k) (b i a k)
                left_inv := fun x => funext fun i => (h1 n i a (x i)).symm
                right_inv := fun f => funext fun i => (h2 n i a _ (f i) rfl).symm
                map_add' := fun x y => funext fun i => coadd n i a (x i) (y i) }
            e_smul := ?_, e_δ := ?_, e_chg := ?_ }⟩
  · intro n a c x i k
    have key : co n i a (c • x i) = fun k => str _ c * co n i a (x i) k := by
      refine (h2 n i a _ _ ?_).symm
      rw [← hstr n i c (x i)]
      conv_lhs => rw [h1 n i a (x i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => (actmul i _ _ _).symm
    exact congrFun key k
  · intro n a b' x i k
    have key : co (n + 1) i (b'.succAbove a) ((resU F (U := capT U' (i ∘ b'.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (x (i ∘ b'.succAbove))) =
        fun k => rs (capO_comp U i b'.succAbove) (co n (i ∘ b'.succAbove) a (x (i ∘ b'.succAbove)) k) := by
      refine (h2 (n + 1) i (b'.succAbove a) _ _ ?_).symm
      conv_lhs => rw [h1 n (i ∘ b'.succAbove) a (x (i ∘ b'.succAbove))]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hres, hb]
    exact congrFun key k
  · intro n a b' x i k
    have key : co n i a (x i) = fun k => ∑ k' : κ (i b'), rs (le_inf (capO_le U i a) (capO_le U i b')) (g (i a) (i b') k k') * co n i b' (x i) k' := by
      refine (h2 n i a _ _ ?_).symm
      have e1 : ∀ k', act i (co n i b' (x i) k') (b i b' k') =
          ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i b')) (g (i a) (i b') k k') * co n i b' (x i) k') (b i a k) := by
        intro k'
        conv_lhs => rw [hg n i a b' k']
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← actmul, mul_comm]
      conv_lhs => rw [h1 n i b' (x i)]
      rw [Finset.sum_congr rfl fun k' _ => e1 k', Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (actsum i _ _ _).symm
    exact congrFun key k

end GlobalTheory.CompanionTheory.CechVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupPowerSmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConePow

theorem cupPowC_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ) : cupPowC A (a • z) k = a ^ k • cupPowC A z k := by
  induction k with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ k ih =>
    change (CH.mulP A).cupC (by omega) (cupPowC A (a • z) k) (a • z) =
      a ^ (k + 1) • (CH.mulP A).cupC (by omega) (cupPowC A z k) z
    rw [ih, map_smul, map_smul, LinearMap.smul_apply, pow_succ', mul_smul]

end GlobalTheory.CompanionTheory.ConePow
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPow
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFiltration

theorem dpow_mem_span_pow {B : Type} [CommRing B] [Algebra ℚ B] {x : B}
    (δ : DividedPowers (Ideal.span {x})) (k : ℕ) {y : B} (hy : y ∈ Ideal.span {x}) :
    δ.dpow k y ∈ Ideal.span {x ^ k} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ δ hy, Algebra.smul_def, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem list_prod_dpow_mem {B : Type} [CommRing B] [Algebra ℚ B] {x : B}
    (δ : DividedPowers (Ideal.span {x})) (l : List (ℕ × B))
    (hl : ∀ q ∈ l, q.2 ∈ Ideal.span {x}) :
    (l.map fun q => δ.dpow q.1 q.2).prod ∈ Ideal.span {x ^ (l.map Prod.fst).sum} := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    have h1 := dpow_mem_span_pow δ q.1 (hl q (by simp))
    have h2 := ih (fun q' hq' => hl q' (by simp [hq']))
    rw [Ideal.mem_span_singleton] at h1 h2 ⊢
    exact mul_dvd_mul h1 h2

theorem dividedPowerFiltration_span_singleton {B : Type} [CommRing B] [Algebra ℚ B] (x : B)
    (δ : DividedPowers (Ideal.span {x})) (r : ℕ) :
    CrystallineSemistableComparison.Pb.pdP δ r = Ideal.span {x ^ r} := by
  apply le_antisymm
  · unfold CrystallineSemistableComparison.Pb.pdP
    rw [Ideal.span_le]
    rintro z ⟨l, hl, hr, rfl⟩
    have h := list_prod_dpow_mem δ l hl
    rw [Ideal.mem_span_singleton] at h
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    exact (pow_dvd_pow x hr).trans h
  · rw [Ideal.span_singleton_le_iff_mem]
    unfold CrystallineSemistableComparison.Pb.pdP
    apply Ideal.subset_span
    refine ⟨List.replicate r (1, x), ?_, ?_, ?_⟩
    · intro q hq
      rw [List.eq_of_mem_replicate hq]
      exact Ideal.mem_span_singleton_self x
    · simp
    · simp [δ.dpow_one (Ideal.mem_span_singleton_self x)]

theorem pdP_γB {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (r : ℕ) :
    pdP (Lat.γB f ξ) r = Ideal.span {f ξ ^ r} :=
  dividedPowerFiltration_span_singleton (f ξ) (Lat.γB f ξ) r

end GlobalTheory.CompanionTheory.DPFiltration
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSemilatticeSystem
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem exists_finite_sys_of_separated_quasiCompact :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s → QuasiCompact s →
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  intro R _ X s hsep hqc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hdiag : IsAffineHom (Limits.pullback.diagonal s) := inferInstance
  have hinf : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => isAffineHom_diagonal_iff.mp hdiag ⊤ (isAffineOpen_top _) U (by simp) V
      (by simp) hU hV
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using isCompact_univ)
  let A : Set X.Opens := infClosure ((fun i : X.affineOpens => i.1) '' S)
  have hA : ∀ U ∈ A, IsAffineOpen U :=
    infClosure_min (t := {U | IsAffineOpen U}) (by rintro _ ⟨i, -, rfl⟩; exact i.2)
      (fun a ha b hb => hinf a b ha hb)
  letI inst : SemilatticeInf A :=
    Subtype.semilatticeInf (fun _ _ ha hb => infClosed_infClosure ha hb)
  haveI hfin : Finite A := ((hS.image _).infClosure).to_subtype
  refine ⟨A, inst, hfin, ⟨⟨fun j => ⟨j.1, hA j.1 j.2⟩, fun a b => rfl, ?_⟩⟩⟩
  apply top_le_iff.mp
  rw [e]
  exact iSup₂_le fun i hi => le_iSup_of_le (⟨i.1, subset_infClosure ⟨i, hi, rfl⟩⟩ : A) le_rfl

end GlobalTheory.CompanionTheory.Axis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueConstantOfCompatibleFamily
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

theorem existsUnique_const_of_trivSqZeroExt (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (bc : BC F F') :
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  intro hS z hz
  choose e he using bc.bij
  have hpure : ∀ (T : C) (r : TrivSqZeroExt R M) (b : F.obj T), e T (r ⊗ₜ[R] b) = r • bc.α T b := by
    intro T r b
    have h : (r ⊗ₜ[R] b : TrivSqZeroExt R M ⊗[R] F.obj T) = r • ((1 : TrivSqZeroExt R M) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h, map_smul, he]
  have hnat : ∀ {T T' : C} (φ : T ⟶ T') (x : TrivSqZeroExt R M ⊗[R] F.obj T),
      e T' ((mp F φ).toLinearMap.lTensor _ x) = mp F' φ (e T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
      rw [LinearMap.lTensor_tmul, hpure, hpure, map_smul]
      exact congrArg (r • ·) (bc.naturality φ b)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  let jj : ∀ T : C, M ⊗[R] F.obj T →ₗ[R] TrivSqZeroExt R M ⊗[R] F.obj T :=
    fun T ↦ (TrivSqZeroExt.inrHom R M).rTensor _
  have hsnd : ∀ (T : C) (x : M ⊗[R] F.obj T),
      (TrivSqZeroExt.sndHom R M).rTensor _ (jj T x) = x := by
    intro T x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcomm : ∀ {T T' : C} (φ : T ⟶ T') (x : M ⊗[R] F.obj T),
      jj T' ((mp F φ).toLinearMap.lTensor M x) = (mp F φ).toLinearMap.lTensor _ (jj T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  have hconst : ∀ (T : C) (r : TrivSqZeroExt R M),
      algebraMap (TrivSqZeroExt R M) (F'.obj T) r = e T (r ⊗ₜ[R] (1 : F.obj T)) := by
    intro T r
    rw [hpure, map_one, Algebra.algebraMap_eq_smul_one]
  let w : C0 F' := fun T ↦ e T (jj T (z T))
  have hw : d0 F' w = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [w, Pi.zero_apply]
    rw [← hnat, ← hcomm, ← hz, sub_self]
  obtain ⟨r, hr⟩ := (hS.1 w).1 hw
  have hjjr : ∀ T : C, jj T (z T) = r ⊗ₜ[R] (1 : F.obj T) := by
    intro T
    apply (e T).injective
    rw [← hconst]
    exact (congrFun hr T).symm
  refine ⟨r.snd, fun T ↦ ?_, fun m₂ hm₂ ↦ ?_⟩
  · rw [← hsnd T (z T), hjjr T]
    simp
  · have h0 : algebraMap (TrivSqZeroExt R M) (C0 F') (TrivSqZeroExt.inr (m₂ - r.snd)) = 0 := by
      funext T
      have hd : (m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have h1 : z T = r.snd ⊗ₜ[R] (1 : F.obj T) := by
          rw [← hsnd T (z T), hjjr T]
          simp
        rw [TensorProduct.sub_tmul, ← hm₂ T, ← h1, sub_self]
      have h2 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have : jj T ((m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T)) =
            (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) := by
          simp [jj]
        rw [← this, hd, map_zero]
      change algebraMap (TrivSqZeroExt R M) (F'.obj T) _ = 0
      rw [hconst, h2, map_zero]
    have h3 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) = 0 :=
      hS.2 (h0.trans (map_zero _).symm)
    have h4 := congrArg TrivSqZeroExt.snd h3
    simpa [sub_eq_zero] using h4

end GlobalTheory.CompanionTheory.Axis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareTransportAlongEquivStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorSquare_transport_along_equiv : ∀ {R : Type} [CommRing R] {V V' W W' : Type} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V'] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] (u : V ≃ₗ[R] V') (v : W ≃ₗ[R] W') (c : V →ₗ[R] V →ₗ[R] W) (c' : V' →ₗ[R] V' →ₗ[R] W') (_ : ∀ a b, v (c a b) = c' (u a) (u b)) (e : ⋀[R]^2 V' ≃ₗ[R] W') (_ : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = c' a b), ∃ e' : ⋀[R]^2 V ≃ₗ[R] W, ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = c a b := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.wedge_transport | exact GlobalTheory.CompanionTheory.HopfC.wedge_transport | (intros; apply GlobalTheory.CompanionTheory.HopfC.wedge_transport <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjectiveStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_cohomology_inclusion_tensor_injective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), H1CommutesBaseChange F → ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective ((iotaQ F).lTensor M) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | exact GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatCocycleTensorRepresentation
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

theorem rTensor_coords_bijective {R : Type} [CommRing R] {I : Type} [Finite I] {P : Type}
    [AddCommGroup P] [Module R P] (M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (e : P ≃ₗ[R] ∀ i, M i) (N : Type) [AddCommGroup N] [Module R N] :
    Function.Bijective (LinearMap.pi fun i =>
      ((LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) ∘ₗ e.toLinearMap).rTensor N) := by
  classical
  cases nonempty_fintype I
  have hcomp : (LinearMap.pi fun i =>
      ((LinearMap.proj i : (∀ i, M i) →ₗ[R] M i) ∘ₗ e.toLinearMap).rTensor N) =
      (TensorProduct.piLeft (R := R) (N := N) (M := M)).toLinearMap ∘ₗ
        (LinearEquiv.rTensor N e).toLinearMap := by
    apply TensorProduct.ext'
    intro p n
    funext i
    simp
  rw [hcomp]
  exact ((LinearEquiv.rTensor N e).trans
    (TensorProduct.piLeft (R := R) (N := N) (M := M))).bijective

section Cochains

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def oneCochainsPiArrowsEquiv : C1 F ≃ₗ[R] ∀ a : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj a.2.1 where
  toFun f a := f a.1 a.2.1 a.2.2
  invFun g T T' φ := g ⟨T, T', φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def twoCochainsPiComposableEquiv : C2 F ≃ₗ[R]
    ∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1 where
  toFun f a := f a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
  invFun g T T' T'' φ ψ := g ⟨T, T', T'', φ, ψ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def evC {T T' : C} (φ : T ⟶ T') : C1 F →ₗ[R] F.obj T' where
  toFun f := f T T' φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_comp_coboundary_one {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (LinearMap.proj (⟨T, T', T'', φ, ψ⟩ : Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')) :
        (∀ a : (Σ T : C, Σ T' : C, Σ T'' : C, (T ⟶ T') × (T' ⟶ T'')), F.obj a.2.2.1) →ₗ[R] _) ∘ₗ
      (twoCochainsPiComposableEquiv F).toLinearMap ∘ₗ d1 F =
    (mp F ψ).toLinearMap ∘ₗ evC F φ - evC F (φ ≫ ψ) + evC F ψ := by
  ext f
  rfl

end Cochains

theorem cocycle_of_flat (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C]
    [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] N)
    (hf : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      f T T'' (φ ≫ ψ) = (mp F ψ).toLinearMap.rTensor N (f T T' φ) + f T' T'' ψ) :
    ∃ t : Z1 F ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = f T T' φ := by
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun _ _ => Finite.of_subsingleton
  have b1 := rTensor_coords_bijective (R := R) _ (oneCochainsPiArrowsEquiv F) N
  have b2 := rTensor_coords_bijective (R := R) _ (twoCochainsPiComposableEquiv F) N
  obtain ⟨v, hv⟩ := b1.2 (fun a => f a.1 a.2.1 a.2.2)
  have hv' : ∀ (T T' : C) (φ : T ⟶ T'), (evC F φ).rTensor N v = f T T' φ := fun T T' φ =>
    congrFun hv ⟨T, T', φ⟩
  have hw : (d1 F).rTensor N v = 0 := by
    apply b2.1
    rw [map_zero]
    funext ⟨T, T', T'', φ, ψ⟩
    have h := congrArg (fun g => LinearMap.rTensor N g v) (evaluation_comp_coboundary_one F φ ψ)
    simp only [LinearMap.rTensor_add, LinearMap.rTensor_sub, LinearMap.rTensor_comp,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, hv'] at h
    rw [hf T T' T'' φ ψ] at h
    simp only [LinearMap.pi_apply, Pi.zero_apply, LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [h]
    abel
  have hex : Function.Exact (Z1 F).subtype (d1 F) := fun x => by
    rw [← LinearMap.mem_ker, ← commAlgFunctorCocyclesOne_eq_ker]
    simp
  obtain ⟨t, ht⟩ := (Module.Flat.rTensor_exact N hex v).1 hw
  refine ⟨t, fun T T' φ => ?_⟩
  have : evZ F φ = evC F φ ∘ₗ (Z1 F).subtype := rfl
  rw [this, LinearMap.rTensor_comp, LinearMap.comp_apply, ht, hv']

end GlobalTheory.CompanionTheory.Axis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InertiaQuotientTransportStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_quotient_equiv_of_matching_places : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.exists_gsIso | exact GlobalTheory.CompanionTheory.PTIso.exists_gsIso | (intros; apply GlobalTheory.CompanionTheory.PTIso.exists_gsIso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeNatDividesLPow
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatticeUnit

theorem natCast_dvd_pow :
    ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
      Lat.Hyp f ξ l m → ∀ n : ℕ, n ≠ 0 →
        ∃ (k : ℕ) (u : Lat.A f ξ l M), (n : Lat.A f ξ l M) * u = (l : Lat.A f ξ l M) ^ k := by
  intro W B _ _ _ f ξ l M m h n hn
  obtain ⟨k, u, hu⟩ := h.unit n hn
  refine ⟨k, Lat.ofW f ξ l M u, ?_⟩
  rw [← map_natCast (Lat.ofW f ξ l M) n, ← map_mul, hu, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.LatticeUnit
end

