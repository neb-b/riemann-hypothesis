module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0013
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAInModPSplit
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_inModP_Bg (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    InModP X p X.B.g S y ↔ InModP X p (gOf p) S y := by
  unfold InModP
  rw [imA_span_Bg X p]

theorem imA_OEp_one (p : TypX X) : (1 : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) ∈ OEp X p :=
  ⟨1, Subring.one_mem _, map_one _⟩

theorem imA_OEp_sub (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s - t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a - b, Subring.sub_mem _ ha hb, map_sub _ _ _⟩

abbrev epsP (p : TypX X) : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E := PI.FinKW.psiV X.B.I p.1 X.ew

theorem imA_eps_mem (p : TypX X) : epsP X p ∈ OEp X p := ⟨X.ew, X.ew_int, rfl⟩

theorem imA_eps_idem (p : TypX X) : epsP X p * epsP X p = epsP X p := by
  unfold epsP
  rw [← map_mul, X.ew_idem]

private theorem latLoc_ringOfIntegers_incl (p : TypX X) (x : 𝓞 X.B.I.E) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((1 : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  unfold latLoc at hu ⊢
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    refine Submodule.subset_span ⟨x • l, X.B.I.L.smul_mem x hl, ?_⟩
    funext i
    simp [ratV, inclR, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

private theorem latLoc_adicIntegers_incl (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h : ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u = c • u := by
    funext i
    simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c hu

theorem imA_lat_OEp (p : TypX X) {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    t • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have key : ∀ b ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E, ∀ w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)),
      PI.FinKW.psiV X.B.I p.1 b • w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro b hb
    unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at hb
    induction hb using Subring.closure_induction with
    | mem z hz =>
      intro w hw
      rcases hz with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
      · obtain ⟨x, rfl⟩ := RingHom.mem_range.mp he
        convert latLoc_ringOfIntegers_incl X p x hw using 2
        simp [PI.FinKW.psiV]
      · have hy' : ∀ v, y v ∈ v.adicCompletionIntegers X.B.I.F := hy
        convert latLoc_adicIntegers_incl X p ⟨y p.1, hy' p.1⟩ hw using 2
        simp [PI.FinKW.psiV] <;> rfl
    | zero => intro w _; simp
    | one => intro w hw; simpa using hw
    | add a b _ _ ha hb => intro w hw; rw [map_add (f := _), add_smul]; exact add_mem (ha w hw) (hb w hw)
    | neg a _ ha => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (ha w hw)
    | mul a b _ _ ha hb => intro w hw; rw [map_mul, mul_smul]; exact ha _ (hb w hw)
  obtain ⟨a, ha, rfl⟩ := ht
  exact key a ha u hu

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfFrameBasis
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed Matrix

theorem reindex_one_mem {R ι n : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (e : n ≃ ι) (I : Ideal R) (M : Matrix n n R) :
    (∀ i j, (Matrix.reindex e e M - 1) i j ∈ I) ↔ ∀ i j, (M - 1) i j ∈ I := by
  have h1 : ∀ i j, (Matrix.reindex e e M - 1) i j = (M - 1) (e.symm i) (e.symm j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have : e.symm i ≠ e.symm j := e.symm.injective.ne hij
      simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne this]
  constructor
  · intro H i j
    have := H (e i) (e j)
    rwa [h1, e.symm_apply_apply, e.symm_apply_apply] at this
  · intro H i j
    rw [h1]; exact H _ _

theorem latGL_genX {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type}
    [Fintype n] [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K)
    (hKB : MassDataIdxCore.KerBack O θ s J P) (hSU : MassDataIdxCore.SurjCore O θ s J P) (c : O) {H : Type} [Group H]
    (m : H →* GL n T) (hmU : ∀ h, m h ∈ Formalism.UG.UJ s J)
    (hK : ∀ h x, x ∈ MassDataIdxCore.Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ MassDataIdxCore.Lat O θ J P)
    (hon : ∀ g : GL n T, g ∈ Formalism.UG.UJ s J →
      (∀ x, x ∈ MassDataIdxCore.Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ MassDataIdxCore.Lat O θ J P) → ∃ h, m h = g) :
    ∃ ψ : H →* GL n O, Function.Surjective ψ ∧ (∀ h, (∀ i j, (((ψ h : GL n O) : Matrix n n O) - 1) i j ∈
      Ideal.span {c}) ↔
      ∀ y ∈ MassDataIdxCore.Lat O θ J P, ∃ z ∈ MassDataIdxCore.Lat O θ J P,
        (((m h : GL n T) : Matrix n n T) - 1) *ᵥ y = (c : K) • z) ∧
      ∀ h, ((ψ h : GL n O) : Matrix n n O).map (algebraMap O K) = MassDataIdxCore.conjPrime₂ θ P (m h) := by
  refine ⟨MassDataIdxCore.psi O θ J P m hK, ?_, fun h => ?_, fun h => MassDataIdxCore.psi_map O θ J P m hK h⟩
  · intro A
    obtain ⟨g, hgU, hgK, hgA⟩ := hSU A
    obtain ⟨h, rfl⟩ := hon g hgU hgK
    refine ⟨h, Units.ext (MassDataIdxCore.map_inj O ?_)⟩
    simp only
    rw [MassDataIdxCore.psi_map, hgA]
  · rw [MassDataIdxCore.psi_ker_iff]
    exact ⟨fun hw => hKB c (m h) (hmU h) (hK h) hw, fun hl => MassDataIdxCore.ker_fwd O θ J P c (m h) hl⟩

set_option maxHeartbeats 1000000 in
theorem latCoreX_holds : LatCoreX := by
  intro D X p θ hθ Q hQ K hK
  obtain ⟨P, hPdef⟩ : ∃ P, P = reindex₂ X p Q := ⟨_, rfl⟩
  rw [← hPdef] at hQ
  obtain ⟨hKB, hSU⟩ := coreAll (FpX X p) (TpX X p) (p.1.adicCompletionIntegers X.B.I.F) (Fin X.B.I.n) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hθ (herm_JR X p) (unit_JR X p)
  have hLat : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := hQ
  let m : K →* GL (Fin X.B.I.n) (TpX X p) :=
    (HR (FpX X p) X.B.I.cm.sig X.B.I.J).subtype.comp K.subtype
  have hmem : ∀ h : K, HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J (h : HAp X p) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro h
    have : (h : HAp X p) ∈ (K : Set (HAp X p)) := h.2
    rw [hK] at this
    exact this
  have hKl : ∀ h x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
      ((m h : GL (Fin X.B.I.n) (TpX X p)) : Matrix _ _ (TpX X p)) *ᵥ x ∈
        MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := by
    intro h x
    rw [← hLat, ← hLat]
    exact hmem h x
  have hon : ∀ g : GL (Fin X.B.I.n) (TpX X p), g ∈ Formalism.UG.UJ (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) →
      (∀ x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
        (g : Matrix _ _ (TpX X p)) *ᵥ x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ
          (JR (FpX X p) X.B.I.J) P) → ∃ h, m h = g := by
    intro g hg hgs
    let x0 : HAp X p := ⟨g, hg⟩
    have hin : x0 ∈ K := by
      rw [← SetLike.mem_coe, hK]
      show g ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
      intro x
      rw [hLat, hLat]
      exact hgs x
    exact ⟨⟨_, hin⟩, rfl⟩
  have hmU : ∀ h, m h ∈ Formalism.UG.UJ (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) :=
    fun h => (h : HAp X p).2
  obtain ⟨ψ0, hψ0s, hker, hform⟩ := latGL_genX (p.1.adicCompletionIntegers X.B.I.F) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hKB hSU ((gOf p : ℕ) : Op X p) m hmU hKl hon
  let φ : GL (Fin X.B.I.n) (Op X p) ≃* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p) :=
    Units.mapEquiv (reindexAlgEquiv (Op X p) (Op X p) (idxEquiv X)).toMulEquiv
  have hv0 : ∀ A : GL (Fin X.B.I.n) (Op X p), ((φ A : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) :
      Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) =
      Matrix.reindex (idxEquiv X) (idxEquiv X) (A : Matrix _ _ (Op X p)) := fun A => rfl
  have hv : ∀ h, (((φ.toMonoidHom.comp ψ0) h : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) :
      Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) =
      Matrix.reindex (idxEquiv X) (idxEquiv X) ((ψ0 h : GL (Fin X.B.I.n) (Op X p)) : Matrix _ _ (Op X p)) := by
    intro h
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact hv0 _
  refine ⟨φ.toMonoidHom.comp ψ0, φ.surjective.comp ?_, fun h => ?_, fun h => ?_⟩
  · exact hψ0s
  · rw [hv, reindex_one_mem]
    rw [hker h]
    have hsm : ∀ z : Fin X.B.I.n → TpX X p,
        (((gOf p : ℕ) : Op X p) : FpX X p) • z = ((gOf p : ℕ) : Op X p) • z := fun z => rfl
    constructor
    · intro H0
      refine ⟨(hmem h), fun y hy => ?_⟩
      obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).1 hy)
      exact ⟨z, (hLat z).2 hz, by rw [← hsm]; exact hz'⟩
    · rintro ⟨-, H0⟩ y hy
      obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).2 hy)
      exact ⟨z, (hLat z).1 hz, by rw [hsm]; exact hz'⟩
  · rw [glRed_coe, hv]
    have e1 : (Matrix.reindex (idxEquiv X) (idxEquiv X)
        ((ψ0 h : GL (Fin X.B.I.n) (Op X p)) : Matrix _ _ (Op X p))).map (algebraMap (Op X p) (FpX X p)) =
        Matrix.reindex (idxEquiv X) (idxEquiv X)
          (((ψ0 h : GL (Fin X.B.I.n) (Op X p)) : Matrix _ _ (Op X p)).map (algebraMap (Op X p) (FpX X p))) := rfl
    rw [e1, hform]
    unfold MassDataIdxCore.conjPrime₂
    rw [← reindex_mul', ← reindex_mul']
    have eP : Matrix.reindex (idxEquiv X) (idxEquiv X) (P : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
        (Q : Matrix _ _ (FpX X p)) := by
      ext i j; simp [hPdef, reindex₂, Matrix.reindex_apply]
    have ePi : Matrix.reindex (idxEquiv X) (idxEquiv X) ((P⁻¹ : GL _ (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
        ((Q⁻¹ : GL _ (FpX X p)) : Matrix _ _ (FpX X p)) := by
      rw [hPdef, reindex₂, ← map_inv]
      ext i j; simp [Matrix.reindex_apply]
    rw [eP, ePi]
    rfl

theorem parabolic_image_of_frame_basis {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_basis_adapted X latCoreX_holds u p h

theorem stImB_of_adaptQ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) :
    StImB X u p :=
  stImB_of X u p (parabolic_image_of_frame_basis X u p h)

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondEmbeddingEqStar
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem sigR_incl (e : X.B.I.E) :
    sigR (FpX X p) X.B.I.cm.sig (inclR (FpX X p) e) = inclR (FpX X p) (star e) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  rfl

theorem secondEmbedding_eq_star (hθ : IsSplitEquiv X p θ) (e : X.B.I.E) : iota2 X p θ e = iota1 X p θ (star e) := by
  have h := hθ (inclR (FpX X p) e)
  rw [sigR_incl, th_incl, th_incl] at h
  have h1 := congrArg Prod.fst h
  simp only [Prod.fst_swap] at h1
  exact h1.symm

theorem unitElt_holds (hθ : IsSplitEquiv X p θ) : UnitElt X p θ := by
  classical
  have hint : ∀ o : 𝓞 X.B.I.E, Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E o)) ≤ 1 := by
    intro o
    have h0 : IsIntegral ℤ (algebraMap (𝓞 X.B.I.E) X.B.I.E o) := RingOfIntegers.isIntegral_coe o
    exact (Valuation.mem_integer_iff _ _).1
      (Valuation.Integers.mem_of_integral (Valuation.integer.integers _)
        (IsIntegral.map_of_comp_eq (Int.castRingHom _) (iota1 X p θ) (RingHom.ext_int _ _) h0))
  have halg : ∀ f : X.B.I.F,
      iota1 X p θ (algebraMap X.B.I.F X.B.I.E f) = algebraMap X.B.I.F (FpX X p) f := by
    intro f
    show (θ (Algebra.TensorProduct.includeRight (algebraMap X.B.I.F X.B.I.E f))).1 = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply X.B.I.F (FpX X p) (TpX X p),
      AlgEquiv.commutes]
    rfl
  let P : Ideal (𝓞 X.B.I.E) :=
    { carrier := {x | Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at hx hy ⊢
        exact Valuation.map_add_lt _ hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hx ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx }
  have hmemP : ∀ x, x ∈ P ↔ Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) < 1 :=
    fun x => Iff.rfl
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : 𝓞 X.B.I.E) ∈ P := by rw [htop]; exact Submodule.mem_top
      rw [hmemP] at h1
      simp at h1
    · intro x y hxy
      rw [hmemP, map_mul, map_mul, Valuation.map_mul] at hxy
      by_contra hn
      rw [not_or, hmemP, hmemP, not_lt, not_lt] at hn
      exact absurd hxy (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2))
  have hPne : P ≠ ⊥ := by
    obtain ⟨f, hfp, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.1.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) f ∈ P := by
      rw [hmemP, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E, halg,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hfp
    rw [hbot, Ideal.mem_bot] at hmem
    apply hf0
    first
    | exact (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (by rw [hmem, map_zero])
    | exact (NoZeroSMulDivisors.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (by rw [hmem, map_zero])
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPne
  obtain ⟨a, t, ht, hat⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
  rw [hmemP, not_lt] at hat
  have hv1 : Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E (a - t))) = 1 :=
    le_antisymm (hint _) hat
  have hdeq : iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E) =
      iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E (a - t)) := by
    rw [secondEmbedding_eq_star X p θ hθ, map_sub, map_sub, ht]
  have hv : Valued.v (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E)) = 1 := by
    rw [hdeq]
    exact hv1
  have hd0 : iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  refine ⟨a, (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E))⁻¹, ?_, inv_mul_cancel₀ hd0⟩
  rw [OpX, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]

theorem herm_entry (i j : Fin X.B.I.n) : star (X.B.I.J i j) = X.B.I.J j i := by
  have h : Formalism.UG.cT (starRingEnd X.B.I.E) X.B.I.J = X.B.I.J := X.B.I.J_herm
  have h2 := congrFun (congrFun h j) i
  simpa only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply] using h2

theorem firstForm_apply (a b : Fin X.B.I.n) : J1 X p θ a b = iota1 X p θ (X.B.I.J a b) := rfl

open scoped Matrix in
theorem dual_gen (hθ : IsSplitEquiv X p θ) (l l' : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L)
    (hl' : l' ∈ X.B.I.L) :
    (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) ∈ OpX X p := by
  have hint : ∀ o : 𝓞 X.B.I.E, iota1 X p θ (o : X.B.I.E) ∈ OpX X p := by
    intro o
    rw [OpX, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have h0 : IsIntegral ℤ ((o : X.B.I.E)) := RingOfIntegers.isIntegral_coe o
    exact (Valuation.mem_integer_iff _ _).1
      (Valuation.Integers.mem_of_integral (Valuation.integer.integers _)
        (IsIntegral.map_of_comp_eq (Int.castRingHom _) (iota1 X p θ) (RingHom.ext_int _ _) h0))
  obtain ⟨o, ho⟩ := (X.B.I.L_dual l).1 hl l' hl'
  have key : (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) =
      iota1 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l' l) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply,
      secondEmbedding_eq_star X p θ hθ, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key, ← ho]
  exact hint o

end Loc

end MassDataIdxSteps
end
end

