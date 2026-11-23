module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FinitelyManyMarkedClassesTermDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
section
noncomputable section

namespace GlobalTheory.KBridge

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def infT : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)


variable (F E) in
def finT : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)


variable (F E) in
def ofInfT : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inl F (Ainf F) (Af F)).rTensor E


variable (F E) in
def ofFinT : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inr F (Ainf F) (Af F)).rTensor E

theorem decomp (z : AF F ⊗[F] E) : z = ofInfT F E (infT F E z) + ofFinT F E (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    conv_lhs => rw [hx, hy]
    abel
  | tmul a e =>
    change a ⊗ₜ[F] e = ((a.1, 0) : AF F) ⊗ₜ[F] e + ((0, a.2) : AF F) ⊗ₜ[F] e
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem tmul_eq_smul_incV {n : ℕ} (a : AF F) (x : Fin n → E) : (fun i => a ⊗ₜ[F] x i) = a • incV F x := by
  funext i
  change a ⊗ₜ[F] x i = a • ((1 : AF F) ⊗ₜ[F] x i)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infT_tmul (a : AF F) (e : E) : infT F E (a ⊗ₜ[F] e) = a.1 ⊗ₜ[F] e := rfl

theorem mem_latHat_iff {n : ℕ} (X : Spc F E n) (z : Fin n → AE F E) :
    z ∈ latHat X ↔ (∀ i, infT F E (z i) = 0) ∧
      (fun i => finT F E (z i)) ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hv, x, hx, rfl⟩ := hz
      have h0 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 ha
      rw [← tmul_eq_smul_incV]
      refine ⟨fun i => ?_, ?_⟩
      · rw [infT_tmul, h0, TensorProduct.zero_tmul]
      · exact AddSubgroup.subset_closure ⟨a.2, fun v => hv v, x, hx, rfl⟩
    | zero =>
      refine ⟨fun i => map_zero _, ?_⟩
      have e : (fun i => finT F E ((0 : Fin n → AE F E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.add_apply, map_add (f := _), hy.1 i, hz.1 i, add_zero]
      · have e : (fun i => finT F E ((y + z) i)) = (fun i => finT F E (y i)) + fun i => finT F E (z i) :=
          funext fun i => map_add _ _ _
        rw [e]; exact add_mem hy.2 hz.2
    | neg y _ hy =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.neg_apply, map_neg, hy.1 i, neg_zero]
      · have e : (fun i => finT F E ((-y) i)) = -fun i => finT F E (y i) := funext fun i => map_neg _ _
        rw [e]; exact neg_mem hy.2
  · rintro ⟨hi, hf⟩
    have e : z = fun i => ofFinT F E (finT F E (z i)) := funext fun i => by
      conv_lhs => rw [decomp (z i)]
      rw [hi i, map_zero, zero_add]
    rw [e]
    suffices H : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)), (fun i => ofFinT F E (y i)) ∈ latHat X from H _ hf
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨show AF F from (0, a), map_zero _, fun v => ha v, x, hx, tmul_eq_smul_incV (show AF F from (0, a)) x⟩
    | zero =>
      have e : (fun i => ofFinT F E ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y y' _ _ hy hy' =>
      have e : (fun i => ofFinT F E ((y + y') i)) = (fun i => ofFinT F E (y i)) + fun i => ofFinT F E (y' i) :=
        funext fun i => map_add _ _ _
      rw [e]; exact add_mem hy hy'
    | neg y _ hy =>
      have e : (fun i => ofFinT F E ((-y) i)) = -fun i => ofFinT F E (y i) := funext fun i => map_neg _ _
      rw [e]; exact neg_mem hy

theorem mulVec_mem_latHat {n : ℕ} (σ : E →ₐ[F] E) (X : Spc F E n) (hfg : X.L.FG) {k : GAd σ X.Jᵀ}
    (hk : k ∈ levelOpen σ X.Jᵀ X.L) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    (matHom (AF F) σ X.Jᵀ k).1 *ᵥ z ∈ latHat X := by
  rw [mem_latHat_iff] at hz ⊢
  obtain ⟨hi, hf⟩ := hz
  refine ⟨fun i => ?_, ?_⟩
  · have e : ((infT F E).toRingHom ∘ z) = 0 := funext fun j => hi j
    refine (RingHom.map_mulVec (infT F E).toRingHom (matHom (AF F) σ X.Jᵀ k).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  · have e : (fun i => finT F E (((matHom (AF F) σ X.Jᵀ k).1 *ᵥ z) i)) =
        Formalism.MainNotions.StandardLattice.finMat σ X.Jᵀ k *ᵥ fun i => finT F E (z i) :=
      funext fun i => RingHom.map_mulVec (finT F E).toRingHom _ _ i
    rw [e]
    exact ((mem_levelOpen_iff_latHat σ X.Jᵀ hfg k).1 hk _).1 hf

theorem ofGAd_mem_stabK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), X.L.IsLattice E → ∀ g : GAd σ X.Jᵀ,
    (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) →
    (∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v) → GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X := by
  intro F E _ _ _ _ _ σ B n X hL g h1 h2
  have hfg : X.L.FG := hL.fg
  have hg : g ∈ levelOpen σ X.Jᵀ X.L := mem_levelOpen.2 h2
  refine ⟨fun w => h1 w, fun z hz => ⟨?_, ?_⟩⟩
  · rw [GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg hg hz
  · rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg (inv_mem hg) hz

end GlobalTheory.KBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkWeightedFixedPointDefinitePairOddOfCounts
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights

theorem exists_root_enum {F : Type} [Field F] (τ : F →+* ℂ) (n : ℕ) :
    ∃ sel : Fin n → Polynomial F → ℂ, ∀ P : Polynomial F, P.Monic → P.natDegree = n →
      (P.map τ).roots = Finset.univ.val.map fun i => sel i P := by
  have key : ∀ P : Polynomial F, ∃ g : Fin n → ℂ, P.Monic → P.natDegree = n →
      (P.map τ).roots = Finset.univ.val.map g := by
    intro P
    by_cases h : P.Monic ∧ P.natDegree = n
    · have hc : (P.map τ).roots.toList.length = n := by
        rw [Multiset.length_toList, ← (IsAlgClosed.splits (P.map τ)).natDegree_eq_card_roots,
          h.1.natDegree_map, h.2]
      obtain ⟨l, hl, hl'⟩ : ∃ l : List ℂ, l.length = n ∧ (P.map τ).roots = (l : Multiset ℂ) :=
        ⟨_, hc, (Multiset.coe_toList _).symm⟩
      subst hl
      exact ⟨l.get, fun _ _ => by rw [Fin.univ_val_map, List.ofFn_get, hl']⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using key
  exact ⟨fun i P => g P i, hg⟩

theorem markWeightedFixedPoint_definitePair_odd_of_counts : GlobalTheory.LKDef.MoveDefInv → GlobalTheory.RootSumWeights.CxCountRegMark → GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne → GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd := by
  intro hmove hcount hfin p _ G ha hn v hv c L f hf hreg K' f' hf' h0
  rw [hcount p G ha v hv c L f hf hreg K' f' hf']
  obtain ⟨sel, hsel⟩ := exists_root_enum v.embedding G.n
  have hmon : ∀ x : G.C, (minpoly G.F x).Monic := fun x => minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ P : Polynomial G.F, P.Monic → P.natDegree = G.n → ∀ μ : ℂ,
      P.eval₂ v.embedding μ = 0 ↔ ∃ i, sel i P = μ := by
    intro P hm hd μ
    rw [← Polynomial.eval_map, ← Polynomial.IsRoot.def, ← Polynomial.mem_roots (hm.map _).ne_zero, hsel P hm hd]
    simp
  have hIs : ∀ i, IsSel G (sel i) := by
    intro i w hw P hm hd
    have hc : Fintype.card {w : InfinitePlace G.F // sigPosH (G.gram_herm w) = 1} = 1 := ha
    obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.1 hc
    have hwv : w = v := congrArg Subtype.val ((hu ⟨w, hw⟩).trans (hu ⟨v, hv⟩).symm)
    subst hwv
    exact (hmem P hm hd _).2 ⟨i, rfl⟩
  have hF := hfin p G ha L f K' f' hf hf'

  have hL : markSumC G c L.K.toSubgroup f K' f' =
      ∑ i, markedSumIrr G (fun P => c P (sel i P)) (sel i) L.K.toSubgroup f 1 K' f' := by
    unfold markSumC markedSumIrr
    rw [← finsum_sum_comm]
    · refine finsum_congr fun q => ?_
      set P : Pair G := Quot.out q
      by_cases hm : ∃ μ, P.Mark μ
      · rw [dite_eq_left hm]
        by_cases hi : Irreducible P.pol
        · have hμ := hm.choose_spec
          obtain ⟨j, hj⟩ := (hmem P.pol (hmon _) P.reg.1 _).1 (mark_isRoot_pol p G P _ ha hμ v hv)
          have hnd : (Finset.univ.val.map fun i => sel i P.pol).Nodup := by
            rw [← hsel P.pol (hmon _) P.reg.1]
            exact Polynomial.nodup_roots (P.reg.2.map)
          have hinj := Multiset.inj_on_of_nodup_map hnd
          rw [Finset.sum_eq_single j]
          · rw [if_pos ⟨hi, hj ▸ hμ⟩]
            beta_reduce
            rw [hj]
          · intro i _ hij
            rw [if_neg]
            rintro ⟨-, hi'⟩
            exact hij (hinj i (Finset.mem_univ_val i) j (Finset.mem_univ_val j)
              ((Pair.mark_unique p G P _ _ ha hi' hμ).trans hj.symm))
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [h0 P hm hi, mul_zero]
          exact (Finset.sum_eq_zero fun i _ => if_neg fun h => hi h.1).symm
      · rw [dite_eq_right hm]
        exact (Finset.sum_eq_zero fun i _ => if_neg fun h => hm ⟨_, h.2⟩).symm
    · intro i _
      refine hF.subset fun q hq => ?_
      rw [Function.mem_support] at hq
      split_ifs at hq with h
      · exact ⟨⟨_, h.2⟩, right_ne_zero_of_mul hq⟩
      · exact absurd rfl hq

  have hD : {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
    obtain ⟨e, he⟩ := cls_equiv_dcls_irr p G ha hn _ (hIs ⟨0, G.n_pos⟩)
    have h1 := (hF.preimage (f := fun q : {q : Cls G // Irreducible (Quot.out q).pol ∧
      (Quot.out q).Mark (sel ⟨0, G.n_pos⟩ (Quot.out q).pol)} => q.1) Subtype.val_injective.injOn).image
      fun q => (e q).1
    refine h1.subset fun d hd => ⟨e.symm ⟨d, hd.1⟩, ⟨⟨_, (e.symm ⟨d, hd.1⟩).2.2⟩, ?_⟩, by simp⟩
    rw [← (he _).2 L.K.toSubgroup f 1 K' f' one_pos hf.2.2.1 hf'.2.2.1, Equiv.apply_symm_apply]
    exact hd.2
  rw [hL, Finset.sum_congr rfl fun i _ =>
    hmove p G ha hn _ _ (hIs i) L.K.toSubgroup f 1 K' f' one_pos hf.2.2.1 hf'.2.2.1]
  unfold dSumIrr
  rw [← finsum_sum_comm]
  · refine finsum_congr fun q => ?_
    set Q : DPair G := Quot.out q
    by_cases hi : Irreducible Q.pol
    · simp only [if_pos hi]
      rw [← Finset.sum_mul, rootSum, hsel Q.pol (hmon _) Q.reg.1, Multiset.map_map]
      rfl
    · simp only [if_neg hi, Finset.sum_const_zero]
  · intro i _
    refine hD.subset fun q hq => ?_
    rw [Function.mem_support] at hq
    split_ifs at hq with h
    · exact ⟨h, right_ne_zero_of_mul hq⟩
    · exact absurd rfl hq

end GlobalTheory.RootSumWeights
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartCentralizerIffTorusIntegralUnits
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.CptInt

open GlobalTheory.UnitLemma

theorem isIntegral_iff_of_mulVec {K : UQ} (B : InvAlg K) {n : ℕ} (φ : B.A ≃ₗ[K.E] (Fin n → K.E)) (a : B.A)
    (M : Matrix (Fin n) (Fin n) K.E) (h : ∀ y, φ (a * y) = M *ᵥ φ y) : IsIntegral K.O a ↔ IsIntegral K.O M := by
  let b : Module.Basis (Fin n) K.E B.A := Module.Basis.ofEquivFun φ
  let f : B.A →ₐ[K.O] Matrix (Fin n) (Fin n) K.E := (Algebra.leftMulMatrix b).restrictScalars K.O
  have hinj : Function.Injective f := Algebra.leftMulMatrix_injective b
  have hf : f a = M := by
    ext i j
    change Algebra.leftMulMatrix b a i j = M i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply, Module.Basis.equivFun_ofEquivFun, h]
    simp [b, Module.Basis.coe_ofEquivFun, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hf]
  exact (isIntegral_algHom_iff f hinj).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with hc
  · exact hc.choose_spec.1
  · exact continuous_id

theorem isClosed_UL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
  unfold UL; rw [if_neg hw]
  have : ((UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Subgroup _) : Set (GLw n w)) =
      (fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
        (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ⁻¹' {1} := rfl
  rw [this]
  refine IsClosed.preimage ?_ isClosed_singleton
  unfold cT
  exact ((((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose).matrix_mul continuous_const).matrix_mul
    Units.continuous_val)

def linModel (w : Pl E) {K : UQ} (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) :
    B.A ≃ₗ[K.E] (Fin n → K.E) where
  toFun y i := e.symm (ψ y i)
  invFun v := ψ.symm fun i => e (v i)
  map_add' y z := by
    funext i
    simp
  map_smul' c y := by
    funext i
    simp [hψ c y]
  left_inv y := by
    simp
  right_inv v := by
    funext i
    simp

theorem linModel_mul (w : Pl E) {K : UQ} (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) {n : ℕ}
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (a : B.A)
    (g : GLw n w) (ha : ∀ y, ψ (a * y) = g.val *ᵥ ψ y) (y : B.A) :
    linModel w e B ψ hψ (a * y) = ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ
      linModel w e B ψ hψ y := by
  funext i
  change e.symm (ψ (a * y) i) = _
  rw [ha]
  exact RingHom.map_mulVec e.symm.toRingHom _ _ i

end GlobalTheory.KapOrb.CptInt

namespace GlobalTheory.KapOrb.CptInt

open GlobalTheory.UnitLemma

theorem mem_cptPart_iff_torusOf_mem_intUnits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (hγ : γ ∈ UL n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h ∈ twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩, (h ∈ cptPart (twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩) ↔ torusOf w B ψ h.1 ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  intro E _ _ _ w hw K e hbr B Q u x n γ hγ ψ hfit hmod h hh
  set T := twCent (MonoidHom.id (UL n w)) ⟨γ, hγ⟩ with hTdef
  have hcomm : ∀ t ∈ T, (t : GLw n w) * γ = γ * t := by
    intro t ht
    have := congrArg Subtype.val (show t * ⟨γ, hγ⟩ = ⟨γ, hγ⟩ * (MonoidHom.id (UL n w)) t from ht)
    simpa using this
  have spec : ∀ t ∈ T, ∀ y, ψ ((torusOf w B ψ (t : GLw n w) : B.A) * y) = (t : GLw n w).val *ᵥ ψ y :=
    fun t ht => (GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute E w hw K e B Q u x n γ ψ hfit hmod t t.2 (hcomm t ht)).2
  have specInv : ∀ t ∈ T, ∀ y, ψ ((((torusOf w B ψ (t : GLw n w))⁻¹ : B.Aˣ) : B.A) * y) =
      ((t : GLw n w)⁻¹).val *ᵥ ψ y := by
    intro t ht y
    have h1 := spec t ht ((((torusOf w B ψ (t : GLw n w))⁻¹ : B.Aˣ) : B.A) * y)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h1
    rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcl := isClosed_UL w hw n
  have hint : ∀ z, z ∈ (algebraMap K.O K.E).range ↔ Valued.v (e z) ≤ 1 := hbr.2.1
  have hmat : ∀ (g : GLw n w) (k : ℕ) i j,
      e ((((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k) i j) =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    intro g k i j
    have : ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) ^ k =
        ((g ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm := by
      rw [Units.val_pow_eq_pow_val]
      exact (map_pow (e.symm.toRingHom.mapMatrix) _ k).symm
    rw [this, Matrix.map_apply, RingEquiv.apply_symm_apply]
  set φ := linModel w e B ψ hmod.1 with hφ
  have key : ∀ s ∈ T, IsCompact (closure (Subgroup.zpowers s : Set (UL n w))) ↔
      torusOf w B ψ (s : GLw n w) ∈ intUnits K.O B.A := by
    intro s hs
    have hI1 : IsIntegral K.O ((torusOf w B ψ (s : GLw n w) : B.Aˣ) : B.A) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v ((((s : GLw n w) ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B φ _ _ (linModel_mul w e B ψ hmod.1 _ _ (spec s hs)), GlobalTheory.IntMatBound.isIntegral_iff_bounded K e hint n]
      simp only [hmat]
    have hI2 : IsIntegral K.O ((((torusOf w B ψ (s : GLw n w))⁻¹ : B.Aˣ) : B.A)) ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j,
        Valued.v ((((s : GLw n w)⁻¹ ^ k : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
          WithZero.exp m := by
      rw [isIntegral_iff_of_mulVec B φ _ _ (linModel_mul w e B ψ hmod.1 _ _ (specInv s hs)), GlobalTheory.IntMatBound.isIntegral_iff_bounded K e hint n]
      simp only [hmat]
    rw [GlobalTheory.T.isCompact_closure_zpowers_iff_bounded_entries w n (UL n w) hcl s]
    show _ ↔ IsIntegral K.O _ ∧ IsIntegral K.O _
    rw [hI1, hI2]
    simp only [SubgroupClass.coe_zpow]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨⟨m, fun k i j => ?_⟩, ⟨m, fun k i j => ?_⟩⟩
      · have := hm (k : ℤ) i j
        rwa [zpow_natCast] at this
      · have := hm (-(k : ℤ)) i j
        rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow] at this
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨max m1 m2, fun k i j => ?_⟩
      rcases Int.eq_nat_or_neg k with ⟨l, rfl | rfl⟩
      · rw [zpow_natCast]
        exact (h1 l i j).trans (WithZero.exp_le_exp.2 (le_max_left _ _))
      · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
        exact (h2 l i j).trans (WithZero.exp_le_exp.2 (le_max_right _ _))
  have tmul : ∀ s ∈ T, ∀ t ∈ T, torusOf w B ψ ((s * t : UL n w) : GLw n w) =
      torusOf w B ψ (s : GLw n w) * torusOf w B ψ (t : GLw n w) := by
    intro s hs t ht
    apply torusOf_spec
    intro y
    rw [Units.val_mul, mul_assoc, spec s hs, spec t ht, Matrix.mulVec_mulVec]
    simp
  have tinv : ∀ s ∈ T, torusOf w B ψ ((s⁻¹ : UL n w) : GLw n w) = (torusOf w B ψ (s : GLw n w))⁻¹ := by
    intro s hs
    apply torusOf_spec
    intro y
    rw [specInv s hs]
    simp
  have tone : torusOf w B ψ ((1 : UL n w) : GLw n w) = 1 := by
    apply torusOf_spec
    intro y
    simp
  let H' : Subgroup (UL n w) :=
    { carrier := {s | s ∈ T ∧ torusOf w B ψ (s : GLw n w) ∈ intUnits K.O B.A}
      one_mem' := ⟨T.one_mem, by rw [tone]; exact (intUnits K.O B.A).one_mem⟩
      mul_mem' := by
        rintro s t ⟨hs, hs'⟩ ⟨ht, ht'⟩
        exact ⟨T.mul_mem hs ht, by rw [tmul s hs t ht]; exact (intUnits K.O B.A).mul_mem hs' ht'⟩
      inv_mem' := by
        rintro s ⟨hs, hs'⟩
        exact ⟨T.inv_mem hs, by rw [tinv s hs]; exact (intUnits K.O B.A).inv_mem hs'⟩ }
  constructor
  · intro hc
    have hle : cptPart T ≤ H' := by
      rw [cptPart, Subgroup.closure_le]
      rintro s ⟨hs, hsc⟩
      exact ⟨hs, (key s hs).1 hsc⟩
    exact (hle hc).2
  · intro hi
    exact Subgroup.subset_closure ⟨hh, (key h hh).2 hi⟩

end GlobalTheory.KapOrb.CptInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNeg
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem natCast_notMem_pow_three_of_quadratic (p : ℕ) (K : Type) [Field K] [NumberField K]
    [Algebra K ℂ] (h2 : Module.finrank ℚ K = 2) (x : K) (hx : x ^ 2 = -(p : K))
    (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯]
    (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)) (hp : p.Prime)
    (hL : IsIntegersLattice p L₀) : (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro hw
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  obtain ⟨⟨⟨hfin, -, hun⟩, -⟩, -⟩ :=
    GlobalTheory.Laid.hcfj_holds K h2 L₀ ((isIntegersLattice_iff hp.pos h2 hx L₀).mp hL)
  have : NumberField K⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite K _
  have hle : ℚ⟮(latticeCurve L₀).j⟯ ≤
      (K⟮(latticeCurve L₀).j⟯.toSubfield.toIntermediateField fun q =>
        SubfieldClass.ratCast_mem _ q) :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self K _)
  let f : ℚ⟮(latticeCurve L₀).j⟯ →+* K⟮(latticeCurve L₀).j⟯ :=
    RingHom.codRestrict (algebraMap ℚ⟮(latticeCurve L₀).j⟯ ℂ) K⟮(latticeCurve L₀).j⟯
      fun z => hle z.2
  obtain ⟨P, hP, hP0, hPp⟩ := _root_.GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom _ _ f w p 3 hw
  exact _root_.GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt p K K⟮(latticeCurve L₀).j⟯ x P hp h2 hx hP0 (hun P hP0) hPp

theorem natCast_notMem_pow_three_adjoin_j : ∀ (p : ℕ) (L₀ : PeriodPair)
    [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)),
    p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro p L₀ _ w hp hL
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField ℚ⟮sqrtNegNat p⟯ := NumberField.of_module_finite ℚ _
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat p)) ^ 2 =
      -(p : ℚ⟮sqrtNegNat p⟯) := Subtype.ext (by simpa using sqrtNegNat_sq p)
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  have h2 : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2 := by
    have hle : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hm : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)).Monic :=
        Polynomial.monic_X_pow_add_C _ two_ne_zero
      have := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ (sqrtNegNat p)
        (p := Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) (by simp [sqrtNegNat_sq])) hm.ne_zero
      rwa [Polynomial.natDegree_X_pow_add_C] at this
    have h1 := IsTotallyComplex.finrank ℚ⟮sqrtNegNat p⟯
    have h3 : 0 < Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ := Module.finrank_pos
    omega
  exact natCast_notMem_pow_three_of_quadratic p _ h2 _ hx L₀ w hp hL

end GlobalTheory.CMModel
end

