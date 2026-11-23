module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLineStableLatticeSplitsAlongWittSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.SplitLat

variable {D : D7}

theorem pair_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_i₀ {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * (d.i₀ *ᵥ y) j = ∑ i, ∑ j, star ((d.q0 *ᵥ x) i) * S₀.gram i j * y j := by
  have hG : S.gram * d.i₀ = d.q0ᴴ * S₀.gram := by
    rw [gram_eq d]
    simp only [Matrix.add_mul, Matrix.mul_assoc, qX_i₀, qY_i₀, wittDecomposition_coreProj_mul_core_eq_one, Matrix.mul_zero, Matrix.mul_one, add_zero,
      zero_add]
  rw [pair_eq_dot, pair_eq_dot, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec]

theorem mulVec_eq_sum_cols {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    M *ᵥ w = ∑ i, fun r => w i * M r i := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem colProj_mulVec' {S : HSp D} {ρ m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E)
    (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) (x : Fin m → D.host.E) :
    colProj q f i *ᵥ x = fun r => (q *ᵥ x) i * f r i := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem selfDual_core_monoAt (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (hcol : ∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) :
    IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by

  have hcore : ∀ y ∈ L, d.q0 *ᵥ y ∈ coreLat d L := by
    intro y hy
    rw [mem_coreLat]
    have hdec : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one_rat, Matrix.one_mulVec]
    have hX : d.e *ᵥ (d.qX *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).1
    have hY : d.e' *ᵥ (d.qY *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).2
    have key : ∀ a b c z : Fin S.rank → D.host.E, z = a + b + c → b = z - a - c := by
      intro a b c z hz; rw [hz]; abel
    have h : d.i₀ *ᵥ (d.q0 *ᵥ y) = y - d.e *ᵥ (d.qX *ᵥ y) - d.e' *ᵥ (d.qY *ᵥ y) := key _ _ _ _ hdec
    rw [h]
    exact sub_mem (sub_mem hy hX) hY
  have hinj : Function.Injective ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) := by
    intro x x' hxx
    have h := congrArg (fun z => d.q0 *ᵥ z) hxx
    simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one,
      Matrix.one_mulVec] using h
  refine ⟨⟨⟨?_, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩, fun v => ?_⟩
  ·
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hLfg : L.FG := hL.1.fg
    haveI : IsNoetherian (𝓞 D.host.E) L := isNoetherian_of_fg_of_noetherian L hLfg
    have hle : (coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ≤ L :=
      Submodule.map_comap_le _ _
    have h1 : (((coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))).comap L.subtype).FG :=
      IsNoetherian.noetherian _
    have h2 := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  ·
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  ·
    obtain ⟨b, hb⟩ := (hL.2 (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
    refine ⟨b, ?_⟩
    rw [hb, pair_i₀, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]
  ·
    rw [mem_coreLat]
    refine (hL.2 (d.i₀ *ᵥ y)).2 fun x hx => ?_
    obtain ⟨b, hb⟩ := h (d.q0 *ᵥ x) (hcore x hx)
    exact ⟨b, hb.trans (pair_i₀ d x y).symm⟩
  ·
    have hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).1
    have hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).2
    intro y
    constructor
    · intro hy
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hX i) _ hy
      · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hY i) _ hy
      · exact rat_mulVec_mem_latV d.q0 hcore _ hy
    · rintro ⟨h1, h3, h2⟩
      have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
          d.sum_eq_one, Matrix.one_mulVec]
      rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
      refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
      exact rat_mulVec_mem_latV d.i₀ (fun x hx => hx) _ h2

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMonomialLatticeSplitCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat

section

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_sec_w (p : SplitPt D k) {m n : ℕ} (a : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    a *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((a.map p.pr *ᵥ y) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, sec_mul_right, mul_comm]

theorem inc_mul_sec_mem_iff (p : SplitPt D k) (α : D.host.E) (x : k) :
    incA D α * p.sec x ∈ intAt D (· = p.v) ↔ p.pr (incA D α) * x ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mul_comm x]
  exact ⟨fun h => (p.int_iff _).2 h.2, sec_mem_intAt p _⟩

theorem proj_mulVec_add {R : Type} [CommRing R] {l m n : ℕ} {P : Matrix (Fin m) (Fin l) R} {J : Matrix (Fin l) (Fin m) R}
    {J' : Matrix (Fin l) (Fin n) R} (h1 : P * J = 1) (h0 : P * J' = 0) (u : Fin m → R) (v : Fin n → R) :
    P *ᵥ (J *ᵥ u + J' *ᵥ v) = u := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

end


set_option maxHeartbeats 1000000 in
theorem wShape_of_mono (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E)
    (L : Lat S) (M : Lat S₀) (N : Lat A) (α α' : Fin ρ → D.host.E) (μ : D.host.E) (g : GA D A)
    (hmono : MonoAt d L M p.v)
    (hX : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jX i a ∈ latV S L (· = p.v) ↔ incA D (α i) * a ∈ intAt D (· = p.v))
    (hY : ∀ i, ∀ a ∈ idAt D (· = p.v), colMul d.jY i a ∈ latV S L (· = p.v) ↔ incA D (α' i) * a ∈ intAt D (· = p.v))
    (hline : LineAt (vecB o ζ) μ M p.v) (hsplit : SplitsAt o M p.v) (htr : TraceAt o g N M p.v) :
    WShape p d o ζ L (fun i => p.pr (incA D (α i))) (fun i => p.pr (incA D (α' i))) (p.pr (incA D μ)) g N := by
  intro x x' t y
  let f : D.host.E →+* k := p.pr.comp (incA D)
  have hz : o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) = p.sec t • ratV (vecB o ζ) := by
    rw [mulVec_sec_w, Matrix.mulVec_smul]
    funext i
    have h := RingHom.map_mulVec f o.iB ζ i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, sec_mul_right]
    exact congrArg (fun u => p.sec (t * u)) h.symm
  obtain ⟨c, hc⟩ : ∃ c : Fin S₀.rank → AE D, c = o.jB *ᵥ (fun i => p.sec ((t • (f ∘ ζ)) i)) +
    o.jA *ᵥ (Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r)) := ⟨_, rfl⟩
  have hcid : ∀ i, c i ∈ idAt D (· = p.v) := fun i => by
    rw [hc, mulVec_sec_w, mulVec_sec_w, mulVec_sec_w]
    exact add_mem (sec_mem_idAt p _) (sec_mem_idAt p _)
  have hvec : (fun r => p.sec ((atW p d.e *ᵥ x + atW p d.e' *ᵥ x' + t • (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A g).map p.pr *ᵥ y)) r)) =
      d.jX *ᵥ (fun i => p.sec (x i)) + d.jY *ᵥ (fun i => p.sec (x' i)) + d.j0 *ᵥ c := by
    have h1 : (fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r'))) = d.i₀.map f *ᵥ (o.iB.map f *ᵥ (f ∘ ζ)) := by
      have h2 : o.iB.map f *ᵥ (f ∘ ζ) = f ∘ vecB o ζ := by
        funext i; exact (RingHom.map_mulVec f o.iB ζ i).symm
      rw [h2]
      funext i; exact RingHom.map_mulVec f d.i₀ _ i
    have h3 : atW p (d.i₀ * o.iA) = d.i₀.map f * o.iA.map f := Matrix.map_mul (f := f)
    rw [hc, Matrix.mulVec_add, h1, h3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
    have e1 : d.jX.map p.pr = atW p d.e := rfl
    have e2 : d.jY.map p.pr = atW p d.e' := rfl
    have e3 : d.j0.map p.pr = d.i₀.map f := rfl
    have e4 : o.jA.map p.pr = o.iA.map f := rfl
    have e5 : o.jB.map p.pr = o.iB.map f := rfl
    rw [mulVec_sec_w p d.jX, mulVec_sec_w p d.jY, mulVec_sec_w p o.jB, mulVec_sec_w p d.j0,
      mulVec_sec_w p (Formalism.L2.Theta.mt A g), mulVec_sec_w p o.jA, mulVec_sec_w p d.j0, e1, e2, e3, e4, e5]
    funext r
    simp only [Pi.add_apply, map_add p.sec, add_assoc]
  rw [hvec, hmono]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, d.pX_jX, d.pX_jY, d.pX_j0, d.pY_jX, d.pY_jY, d.pY_j0, d.p0_jX,
    d.p0_jY, d.p0_j0, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  have hA : o.pA *ᵥ c = Formalism.L2.Theta.mt A g *ᵥ fun r => p.sec (y r) := by
    rw [hc, add_comm]; exact proj_mulVec_add o.pA_jA o.pA_jB _ _
  have hB : o.pB *ᵥ c = fun i => p.sec ((t • (f ∘ ζ)) i) := by
    rw [hc]; exact proj_mulVec_add o.pB_jB o.pB_jA _ _
  rw [hsplit c hcid, hA, hB, hz, hline _ (sec_mem_idAt p t), ← htr _ (fun i => sec_mem_idAt p _), inc_mul_sec_mem_iff]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) and_comm)
  · rw [hX i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]
  · rw [hY i _ (sec_mem_idAt p _), inc_mul_sec_mem_iff]

end GlobalTheory.Core.Mi.LatMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjugateStabilizerKeepsMovedFrameLatt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.StMoves

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_mul {m n p : Type} [Fintype n] {A : Matrix m n k} {B : Matrix n p k} (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) : ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j =>
  Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

theorem int_one_sub {m a b : Type} [DecidableEq m] (f : a → m) (g' : b → m) :
    ∀ i j, ((1 : Matrix m m k).submatrix f g') i j ∈ 𝒪[k] := fun i j => by
  change (1 : Matrix m m k) (f i) (g' j) ∈ 𝒪[k]
  rw [Matrix.one_apply]
  split_ifs
  exacts [Subring.one_mem _, Subring.zero_mem _]

theorem mt_mul (S : HSp D) (a b : GA D S) : mt S (a * b) = mt S a * mt S b := by simp [Formalism.L2.Theta.mt]

theorem alg_frame {n : ℕ} {Y R A' : Type} [Fintype Y] [DecidableEq Y] [CommRing R] [CommRing A'] (pr : R →+* k) (toE : R →+* A')
    (π : A' →+* k) (hmap : ∀ x, π (toE x) = pr x) (mg mt' mh b : Matrix (Fin n) (Fin n) R) (βv I : Matrix (Fin n) (Fin n) A')
    (Fβ : Matrix (Fin n) Y k) (Fγ : Matrix Y (Fin n) k) (e : Y ≃ Fin n) (hγβ : Fγ * Fβ = 1) (hb : b.map toE = βv)
    (hmv : (mt' * b).map pr = Fβ.submatrix id e.symm) (hg1 : mg * mt' = mt' * mh) (hfin : mh.map toE * βv = βv * I) :
    Fγ * mg.map pr * Fβ = (1 : Matrix Y Y k).submatrix id e.symm * I.map π * (1 : Matrix Y Y k).submatrix e.symm id := by
  have hm : ∀ N : Matrix (Fin n) (Fin n) R, (N.map toE).map π = N.map pr := fun N => Matrix.ext fun _ _ => hmap _
  have eq2 : mg.map pr * Fβ.submatrix id e.symm = Fβ.submatrix id e.symm * I.map π := by
    rw [← hmv, ← Matrix.map_mul, ← Matrix.mul_assoc, hg1, Matrix.mul_assoc, Matrix.map_mul, ← hm (mh * b), Matrix.map_mul,
      hb, hfin, Matrix.map_mul, ← hb, hm, ← Matrix.mul_assoc, ← Matrix.map_mul]
  have eq1 : Fβ = Fβ.submatrix id e.symm * (1 : Matrix Y Y k).submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]; rfl
  have eq3 : Fγ * Fβ.submatrix id e.symm = (1 : Matrix Y Y k).submatrix id e.symm := by
    rw [← hγβ]
    exact Matrix.submatrix_mul_equiv Fγ Fβ id (Equiv.refl _) e.symm
  conv_lhs => rw [eq1]
  rw [Matrix.mul_assoc Fγ, ← Matrix.mul_assoc _ (Fβ.submatrix id e.symm), eq2, ← eq3]
  simp only [Matrix.mul_assoc]

theorem int_of_mem_St (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y)
    (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank)
    (hM : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm))
    (g : GA D S) (hg : Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β) :
    ∀ i j, (F.γ * (mt S g).map q.pr * F.β) i j ∈ 𝒪[k] := by
  obtain ⟨Y0, hY0⟩ := hg
  obtain ⟨π, h1, -, h3, -⟩ := GlobalTheory.LocMod.LevBack.exists_chart q hq
  have hb' : (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map (toEAf D) = β.val :=
    Matrix.ext fun _ _ => GlobalTheory.LocMod.LevBack.toEAf_finEmb _
  have hmv : (mt S t * β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map q.pr = F.β.submatrix id e.symm := hM _ hb'
  have hZi : ∀ i j, ((Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val.map π) i j ∈ 𝒪[k] := fun i j => h3 (Y0.val i j)
  have hmap : ∀ N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (N.map (toEAf D)).map π = N.map q.pr :=
    fun N => Matrix.ext fun _ _ => h1 _
  have hfin : Lev.finE S (t⁻¹ * g * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0 := by
    rw [← hY0]
    simp [Formalism.L2.DIV.frGL]
  have hfin' : (mt S (t⁻¹ * g * t)).map (toEAf D) * β.val = β.val * (Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val := by
    have := congrArg Units.val hfin
    rwa [Units.val_mul, Units.val_mul] at this
  have hg1 : mt S g * mt S t = mt S t * mt S (t⁻¹ * g * t) := by
    rw [← mt_mul, ← mt_mul]; congr 1; group
  rw [alg_frame q.pr (toEAf D) π h1 (mt S g) (mt S t) (mt S (t⁻¹ * g * t)) (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)) β.val
    (Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val F.β F.γ e F.γβ hb' hmv hg1 hfin']
  exact int_mul (int_mul (int_one_sub _ _) hZi) (int_one_sub _ _)


open scoped Pointwise in
theorem moves_of_mem_St : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y), (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) → ∀ (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm) → ∀ g : GA D S, Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β → GlobalTheory.FinPl.Moves S g L L (· = q.v) := by
  intro D k _ _ _ _ q PP hq S L hL Y _ _ F hF t β e hM g hg
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k q S Y F.β F.γ F.βγ F.γβ
  have hlat : (⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩ : GlobalTheory.FinPl.Frame q S Y).IsLat L (GlobalTheory.StepData.latOf 1) := fun x => by
    rw [GlobalTheory.StepData.mem_latOf_one]; exact hF x
  refine (_root_.GlobalTheory.FrameMoves.moves_iff_smul D k q S Y _ L _ hL hlat g).2 ?_
  have hA : ∀ i j, (GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g).val i j ∈ 𝒪[k] :=
    int_of_mem_St q hq S F t β e hM g hg
  have hAi : ∀ i j, ((GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g)⁻¹).val i j ∈ 𝒪[k] := by
    rw [← map_inv]
    refine int_of_mem_St q hq S F t β e hM g⁻¹ ?_
    have : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
    rw [this, map_inv]
    exact Subgroup.inv_mem _ hg
  have hK : GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g ∈ GlobalTheory.StepData.stabLat 1 := by
    rw [GlobalTheory.StepData.mem_stabLat, inv_one, one_mul, mul_one]
    exact GlobalTheory.StepData.mem_KO.2 ⟨hA, hAi⟩
  have hs := GlobalTheory.StepData.mem_stabLat_iff.1 hK
  set A := GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g
  ext y
  conv_rhs => rw [← hs]
  change (∃ x, x ∈ GlobalTheory.StepData.latOf 1 ∧ A • x = y) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (GlobalTheory.StepData.mulVec_mem_latOf A).2 hx
  · intro hy
    refine ⟨A⁻¹ • y, (GlobalTheory.StepData.mulVec_mem_latOf A).1 ?_, smul_inv_smul _ _⟩
    have : A.val *ᵥ (A⁻¹ • y) = y := smul_inv_smul A y
    rwa [this]

end GlobalTheory.LocMod.StMoves
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHomLatticeCompletionOpenCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.OpenCompactLat

theorem isOpen_isCompact_of_nsmul {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {Y Y' : Type}
    (A A₀ : AddSubgroup (Matrix Y Y' k)) (ho : IsOpen (A₀ : Set (Matrix Y Y' k)))
    (hc : IsCompact (A₀ : Set (Matrix Y Y' k))) (M N : ℕ) (hM : (M : k) ≠ 0) (hN : (N : k) ≠ 0)
    (h1 : ∀ x ∈ A, M • x ∈ A₀) (h2 : ∀ y ∈ A₀, N • y ∈ A) :
    IsOpen (A : Set (Matrix Y Y' k)) ∧ IsCompact (A : Set (Matrix Y Y' k)) := by
  have hU : IsOpen ((fun x : Matrix Y Y' k => (N : k) • x) '' (A₀ : Set (Matrix Y Y' k))) :=
    (Homeomorph.smulOfNeZero (N : k) hN).isOpenMap _ ho
  have hA : IsOpen (A : Set (Matrix Y Y' k)) := by
    refine A.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds ⟨0, A₀.zero_mem, smul_zero _⟩) ?_)
    rintro _ ⟨y, hy, rfl⟩
    change (N : k) • y ∈ A
    rw [Nat.cast_smul_eq_nsmul]
    exact h2 y hy
  refine ⟨hA, IsCompact.of_isClosed_subset (hc.image (continuous_const_smul ((M : k)⁻¹))) (A.isClosed_of_isOpen hA) ?_⟩
  intro x hx
  refine ⟨M • x, h1 x hx, ?_⟩
  change (M : k)⁻¹ • (M • x) = x
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hM, one_smul]

theorem openCompact : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T), Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), IsOpen (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) ∧ IsCompact (((latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)).comap (GlobalTheory.LocMod.Witness.upH (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) := by
  intro D k _ _ _ _ p S T LS LT hLS hLT Y Y' _ _ _ _ FS FT
  have hF := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hG := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  letI := hLS
  letI := hLT
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hF
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hG
  obtain ⟨M, hM, hM'⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO
    (ΛS' := GlobalTheory.PlaceModel.latFrame S) (ΛT' := GlobalTheory.PlaceModel.latFrame T)
    hLS.toIsLattice.fg hLT.toIsLattice.fg inferInstance inferInstance
  obtain ⟨N, hN, hN'⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (ΛS' := LS) (ΛT' := LT)
    hF.1.fg hG.1.fg inferInstance inferInstance
  have hcast : ∀ n : ℕ, 0 < n → (n : k) ≠ 0 := fun n hn => by
    have h0 : IsUnit (n : D.host.E) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    have h1 := (h0.map (incA D)).map p.pr
    rw [map_natCast, map_natCast] at h1
    exact h1.ne_zero
  refine isOpen_isCompact_of_nsmul _ _ (GlobalTheory.LocMod.Witness.lat_open (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT hF hG)
    (GlobalTheory.LocMod.Witness.lat_compact (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT hF hG) M N (hcast M hM) (hcast N hN) ?_ ?_
  · intro x hx
    rw [AddSubgroup.mem_comap] at hx ⊢
    rw [map_nsmul]
    exact hM' _ (GlobalTheory.PlaceModel.latO_le_top _ hx)
  · intro y hy
    rw [AddSubgroup.mem_comap] at hy ⊢
    refine GlobalTheory.SplitLinAt.latHalf D k p S T LS LT _ ?_ (Or.inl ?_)
    · rw [map_nsmul]
      exact hN' _ hy
    · exact GlobalTheory.LocMod.Witness.up_half (GlobalTheory.LocMod.Place.ofSplitPt p) FS FT _

end GlobalTheory.OpenCompactLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionInvariantPairFunctionalResidue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

theorem latPair_hasVal_residue_of_transvections : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 2 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → ∃ ε : 𝓀[k], ε ≠ 0 ∧ ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]), P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * ε) := by
  intro k _ _ _ _ n _ _ i P c _hcard hc hlat hcl
  classical
  set e : n → (n → k) := fun b => c • (Pi.single b (1:k) : n → k) with he_def
  have hcoef : ∀ b j, c⁻¹ * e b j = (Pi.single b (1:k) : n → k) j := by
    intro b j
    by_cases h : j = b
    · subst h; simp [he_def, hc]
    · simp [he_def, Pi.single_apply, h]
  have hmem : ∀ b, e b ∈ P.lat := fun b => (hlat _).2 (fun j => by
    rw [hcoef]
    by_cases h : j = b
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_apply, h, if_false]; exact zero_mem _)
  let v : n → 𝓀[k] := fun b => P.fn ⟨e b, hmem b⟩
  have hv : ∀ b, P.HasVal (e b) (v b) := fun b => P.hasVal_fn ⟨e b, hmem b⟩
  have hzero : ∀ a, a ≠ i → v a = 0 := by
    intro a ha
    have h1 := hcl (e i) (v i) (hv i) a i 1 ha (Or.inl ha)
    have h2 : e i + Pi.single a (((1:𝒪[k]) : k) * e i i) = e i + e a := by
      congr 1
      funext j
      by_cases h : j = a
      · subst h; simp [he_def]
      · simp [he_def, Pi.single_apply, h]
    rw [h2] at h1
    have h3 := h1.sub (hv i)
    rw [add_sub_cancel_left, sub_self] at h3
    exact (hv a).unique h3
  have hsum : ∀ (s : n → 𝒪[k]) (S : Finset n),
      P.HasVal (∑ b ∈ S, s b • e b) (∑ b ∈ S, IsLocalRing.residue 𝒪[k] (s b) * v b) := by
    intro s S
    induction S using Finset.induction_on with
    | empty => simpa using (hv i).sub (hv i)
    | insert b S hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      exact ((hv b).smul (s b)).add ih
  have hval : ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]),
      P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * v i) := by
    intro x hx
    let s : n → 𝒪[k] := fun b => ⟨c⁻¹ * x b, hx b⟩
    have hx' : (∑ b, s b • e b) = x := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · change ((s j : 𝒪[k]) : k) * (c * (Pi.single j (1:k) : n → k) j) = x j
        simp only [s, Pi.single_eq_same, mul_one]
        field_simp
      · intro b _ hb
        change ((s b : 𝒪[k]) : k) * (c * (Pi.single b (1:k) : n → k) j) = 0
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    have := hsum s Finset.univ
    rw [hx', Finset.sum_eq_single i (fun b _ hb => by rw [hzero b hb, mul_zero]) (by simp)] at this
    exact this
  refine ⟨v i, ?_, hval⟩
  intro h0
  apply P.fn_ne
  refine LinearMap.ext fun y => ?_
  have := hval y ((hlat y).1 y.2)
  rw [h0, mul_zero] at this
  exact (P.hasVal_fn y).unique this

end GlobalTheory
end

