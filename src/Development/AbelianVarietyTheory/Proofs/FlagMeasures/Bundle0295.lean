module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameConditionCharacterLocal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeConcreteDataEqAdelicSpan
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.St.G

theorem latTransport : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ w : Fin X.B.I.n → D.host.E ⊗[D.host.F] Ad D.host.F, w ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) ↔ (fun i => ιA.symm (w i)) ∈ X.B.I.Lf := by
  intro D X ιA hA w
  obtain ⟨h1, h2⟩ := hA
  have hgen : ∀ x : X.B.I.E, ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x)) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x := by
    intro x; rw [RingEquiv.symm_apply_eq]; exact (h1 x).symm
  have hgen' : ∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x) := h1
  have hint : ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ OAd D.host.F D.host.E := h2
  have hL' : ∀ c : Fin X.B.I.n → D.host.E,
      c ∈ (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) ↔
        (fun i => X.ιE.symm (c i)) ∈ X.B.I.L := by
    intro c
    rw [X.L_eq, Submodule.mem_comap]
    simp [Fintype.linearCombination_apply]
  constructor
  · intro hw
    change w ∈ Submodule.span _ _ at hw
    change (fun i => ιA.symm (w i)) ∈ Submodule.span _ _
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine Submodule.subset_span ⟨⟨fun i => X.ιE.symm (c i), (hL' c).1 hc⟩, ?_⟩
      funext i
      simp only
      rw [← hgen, RingEquiv.apply_symm_apply]
    | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
    | add x y _ _ hx hy =>
      have : (fun i => ιA.symm ((x + y) i)) = (fun i => ιA.symm (x i)) + (fun i => ιA.symm (y i)) := by
        funext i; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hr : ιA.symm (r : D.host.E ⊗[D.host.F] Ad D.host.F) ∈ IntAf X.B.I.F X.B.I.E := by
        rw [hint, RingEquiv.apply_symm_apply]; exact r.2
      have : (fun i => ιA.symm ((r • x) i)) = (⟨_, hr⟩ : IntAf X.B.I.F X.B.I.E) • (fun i => ιA.symm (x i)) := by
        funext i; simp [Subring.smul_def, smul_eq_mul, map_mul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro hw
    change _ ∈ Submodule.span _ _ at hw
    change w ∈ Submodule.span _ _
    have key : ∀ v, v ∈ Submodule.span (IntAf X.B.I.F X.B.I.E)
        (Set.range fun x : X.B.I.L => fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((x : Fin X.B.I.n → X.B.I.E) i)) →
        (fun i => ιA (v i)) ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
      intro v hv
      change _ ∈ Submodule.span _ _
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        refine Submodule.subset_span ⟨fun i => X.ιE ((x : Fin X.B.I.n → X.B.I.E) i), (hL' _).2 ?_, ?_⟩
        · simpa using x.2
        · funext i; simp only; rw [hgen']
      | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
      | add x y _ _ hx hy =>
        have : (fun i => ιA ((x + y) i)) = (fun i => ιA (x i)) + (fun i => ιA (y i)) := by
          funext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have hr : ιA (r : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hint _).1 r.2
        have : (fun i => ιA ((r • x) i)) = (⟨_, hr⟩ : OAd D.host.F D.host.E) • (fun i => ιA (x i)) := by
          funext i; simp [Subring.smul_def, smul_eq_mul, map_mul]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key _ hw
    have e : (fun i => ιA (ιA.symm (w i))) = w := funext fun i => by simp
    rw [e] at this
    exact this

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameComponentLocalFrameStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeFrame_component_localFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  first | exact @GlobalTheory.St.G.frame_component_local | exact GlobalTheory.St.G.frame_component_local | (intros; apply GlobalTheory.St.G.frame_component_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameConditionCharacterLocalStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeFrame_condition_character_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k : ℕ) (gp : Fin 2 → ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → IsLat L → (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ y : GL (Fin n) (E ⊗[F] Ad F), y ∈ stabGL (hat F L) → ((∀ i : Fin k, InModL (hat F L) (gp 0 * gp 1) (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)) ↔ ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Fr.LocK L v (bc (prV (E := E) v) y)) ∧ Fr.chi y = ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (gp i : 𝓞 F) ∈ v.asIdeal), Fr.locChi v (bc (prV (E := E) v) y) := by
  first | exact @GlobalTheory.St.G.frame_local | exact GlobalTheory.St.G.frame_local | (intros; apply GlobalTheory.St.G.frame_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalIsometricDefiniteModel
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.ModelIso

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fixedFrameOfWord_castSucc_eq_hyperbolic (a : Fin D.R.rS) : (GlobalTheory.TypeAsm.F0 X u).e a.castSucc = X.eX a := by
  show (lf D (X.Fu u)).fl.fvec a.castSucc = X.eX a
  rw [GlobalTheory.TypeAsm.fv_cast]
  exact congrFun (X.Fu_e u) a

theorem fixedFrameOfWord_last_eq_anisotropic : (GlobalTheory.TypeAsm.F0 X u).e (Fin.last _) = X.zu u := by
  show (lf D (X.Fu u)).fl.fvec (Fin.last _) = X.zu u
  rw [GlobalTheory.TypeAsm.fv_last]
  exact X.flagZVector u

theorem fixedFrameOfWord_isotropicSpan_eq : (GlobalTheory.TypeAsm.F0 X u).X = Submodule.span D.host.E (Set.range X.eX) := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, fixedFrameOfWord_castSucc_eq_hyperbolic]
  exact ⟨fun ⟨b, _, h⟩ => ⟨b, h⟩, fun ⟨b, h⟩ => ⟨b, b.isLt, h⟩⟩

theorem hT_span_left {v : (VS D).V} (hv : ∀ a, (VS D).hT (X.eX a) v = 0) {y : (VS D).V}
    (hy : y ∈ Submodule.span D.host.E (Set.range X.eX)) : (VS D).hT y v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, hv]

theorem hT_span_span {y y' : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range X.eX))
    (hy' : y' ∈ Submodule.span D.host.E (Set.range X.eX)) : (VS D).hT y y' = 0 := by
  refine hT_span_left X (fun a => ?_) hy
  exact p_symm_zero (VS D) (hT_span_left X (fun b => X.ee b a) hy')

theorem hT_f_e (a b : Fin D.R.rS) : (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
  rw [a_herm (S := VS D) (X.eX a) (X.fY b), X.ef a b]
  split_ifs <;> simp

theorem span_eq_zero {d : (VS D).V} (hd : d ∈ Submodule.span D.host.E (Set.range X.eX))
    (h : ∀ b, (VS D).hT (X.fY b) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hd
  have hc : ∀ b, c b = 0 := by
    intro b
    have := h b
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hT_f_e] using this
  simp [hc]

end GlobalTheory.RowsOrb.ModelIso

namespace GlobalTheory.RowsOrb.ModelIso

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def corr (W : Submodule D.host.E (VS D).V) : W →ₗ[D.host.E] (VS D).V :=
  ∑ a, LinearMap.smulRight (((VS D).hT (X.fY a)).comp W.subtype) (X.eX a)

theorem corr_apply (W : Submodule D.host.E (VS D).V) (w : W) :
    corr X W w = ∑ a, (VS D).hT (X.fY a) (w : (VS D).V) • X.eX a := by
  simp [corr, LinearMap.sum_apply]

theorem corr_mem (W : Submodule D.host.E (VS D).V) (w : W) :
    corr X W w ∈ Submodule.span D.host.E (Set.range X.eX) := by
  rw [corr_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.RowsOrb.ModelIso


open GlobalTheory.RowsOrb.ModelIso in
theorem GlobalTheory.RowsOrb.ub_equiv_model : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (GlobalTheory.TypeAsm.F0 X u) HW W.subtype →
    ∃ e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W, (∀ x y, HW.B.flip (e x) (e y) = GlobalTheory.RowsOrb.hU X u x y) ∧
      ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X := by
  intro D X u W HW hE

  have hWe : ∀ (w : W) a, (VS D).hT (X.eX a) (w : (VS D).V) = 0 := by
    intro w a
    have h := ((hE.2 (w : (VS D).V)).2 (Submodule.mem_sup_left ⟨w, rfl⟩)) a.castSucc
    change (VS D).hT (w : (VS D).V) ((GlobalTheory.TypeAsm.F0 X u).e a.castSucc) = 0 at h
    rw [fixedFrameOfWord_castSucc_eq_hyperbolic] at h
    exact p_symm_zero (VS D) h
  have hWz : ∀ w : W, (VS D).hT (X.zu u) (w : (VS D).V) = 0 := by
    intro w
    have h := ((hE.2 (w : (VS D).V)).2 (Submodule.mem_sup_left ⟨w, rfl⟩)) (Fin.last _)
    change (VS D).hT (w : (VS D).V) ((GlobalTheory.TypeAsm.F0 X u).e (Fin.last _)) = 0 at h
    rw [fixedFrameOfWord_last_eq_anisotropic] at h
    exact p_symm_zero (VS D) h
  have hXW : ∀ (w : W) {y : (VS D).V}, y ∈ Submodule.span D.host.E (Set.range X.eX) →
      (VS D).hT y (w : (VS D).V) = 0 ∧ (VS D).hT (w : (VS D).V) y = 0 := by
    intro w y hy
    have h := hT_span_left X (hWe w) hy
    exact ⟨h, p_symm_zero (VS D) h⟩
  have hBW : ∀ x y : W, HW.B x y = (VS D).hT (y : (VS D).V) (x : (VS D).V) := fun x y => (hE.1 x y).symm

  have hmWb : ∀ w : W, (w : (VS D).V) - corr X W w ∈ GlobalTheory.RowsOrb.Wb X := by
    intro w
    rw [GlobalTheory.RowsOrb.mem_Wb]
    intro b
    have hc := corr_mem X W w
    refine ⟨?_, ?_⟩
    · rw [map_sub, hWe w b, zero_sub, neg_eq_zero]
      exact p_symm_zero (VS D) (hT_span_left X (fun a => X.ee a b) hc)
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, corr_apply, map_sum]
        simp only [map_smul, hT_f_e, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, sub_self]
  have hmUb : ∀ w : W, (⟨(w : (VS D).V) - corr X W w, hmWb w⟩ : GlobalTheory.RowsOrb.Wb X) ∈ GlobalTheory.RowsOrb.Ub X u := by
    intro w
    rw [GlobalTheory.RowsOrb.mem_Ub]
    change (VS D).hT (X.zu u) ((w : (VS D).V) - corr X W w) = 0
    rw [map_sub, hWz w, zero_sub, neg_eq_zero]
    refine p_symm_zero (VS D) (hT_span_left X (fun a => (X.zu_orth u a).1) (corr_mem X W w))
  let g : W →ₗ[D.host.E] GlobalTheory.RowsOrb.Ub X u :=
    { toFun := fun w => ⟨⟨(w : (VS D).V) - corr X W w, hmWb w⟩, hmUb w⟩
      map_add' := fun x y => by ext; simp only [Submodule.coe_add, map_add (f := _)]; abel
      map_smul' := fun c x => by ext; simp [smul_sub] }
  have hg : ∀ w, (((g w : GlobalTheory.RowsOrb.Wb X)) : (VS D).V) = (w : (VS D).V) - corr X W w := fun _ => rfl
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : (w : (VS D).V) = corr X W w := by
      have := congrArg (fun x : GlobalTheory.RowsOrb.Ub X u => ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V)) hw
      simp only [hg, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.1 this
    have hmem : (w : (VS D).V) ∈ Submodule.span D.host.E (Set.range X.eX) := h0 ▸ corr_mem X W w
    exact HW.nondeg w fun y => by rw [hBW]; exact (hXW y hmem).2
  have hsurj : Function.Surjective g := by
    intro x
    have hv : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = 0 := by
      intro a
      change (VS D).hT _ ((GlobalTheory.TypeAsm.F0 X u).e a) = 0
      refine Fin.lastCases ?_ (fun b => ?_) a
      · rw [fixedFrameOfWord_last_eq_anisotropic]; exact p_symm_zero (VS D) ((GlobalTheory.RowsOrb.mem_Ub X u _).1 x.2)
      · rw [fixedFrameOfWord_castSucc_eq_hyperbolic]; exact p_symm_zero (VS D) ((((x : GlobalTheory.RowsOrb.Wb X)).2 b).1)
    obtain ⟨y, ⟨w, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 ((hE.2 _).1 hv)
    refine ⟨w, ?_⟩
    rw [fixedFrameOfWord_isotropicSpan_eq] at hz
    have hd : ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) - ((g w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = 0 := by
      apply span_eq_zero X
      · rw [hg, ← hyz]
        have : (W.subtype w + z) - ((w : (VS D).V) - corr X W w) = z + corr X W w := by
          simp only [Submodule.subtype_apply]; abel
        rw [this]
        exact Submodule.add_mem _ hz (corr_mem X W w)
      · intro b
        exact ((Submodule.sub_mem _ (x : GlobalTheory.RowsOrb.Wb X).2 (g w : GlobalTheory.RowsOrb.Wb X).2) b).2
    ext
    exact (sub_eq_zero.1 hd).symm
  let e := (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).symm
  have hge : ∀ x, g (e x) = x := fun x => (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).apply_symm_apply x
  have hxe : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = ((e x : W) : (VS D).V) - corr X W (e x) := by
    intro x
    rw [← hg (e x), hge x]
  refine ⟨e, fun x y => ?_, fun x => ?_⟩
  · rw [LinearMap.flip_apply, hBW, GlobalTheory.RowsOrb.hU_apply, hxe x, hxe y]
    have h1 := (hXW (e y) (corr_mem X W (e x))).1
    have h2 := (hXW (e x) (corr_mem X W (e y))).2
    have h3 := hT_span_span X (corr_mem X W (e x)) (corr_mem X W (e y))
    simp only [map_sub, LinearMap.sub_apply, h1, h2, h3, sub_zero]
  · rw [hxe x, sub_sub_cancel, fixedFrameOfWord_isotropicSpan_eq]
    exact corr_mem X W (e x)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalTotallyPositiveDefinite
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb

variable {D : D7}

theorem eq_zero_of_mem_span_eX (X : HidaSetting D) (w : (VS D).V)
    (hw : w ∈ Submodule.span D.host.E (Set.range X.eX)) (hf : ∀ b, (VS D).hT (X.fY b) w = 0) : w = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hw
  have hc : ∀ b, c b = 0 := by
    intro b
    have h := hf b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul] at h
    have hfe : ∀ a, (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
      intro a
      rw [a_herm, X.ef a b]
      split_ifs <;> simp
    simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  simp [hc]

theorem pd_hU : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.Mass.PD (GlobalTheory.RowsOrb.hU X u) := by
  intro D X u τ x hx
  have hpos : (GlobalTheory.TypeAsm.F0 X u).PosDefAt τ :=
    Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (GlobalTheory.TypeAsm.tu_ne D u)
      (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) τ
  set w : (VS D).V := ((x : Wb X) : (VS D).V) with hwdef
  have hWb := (mem_Wb X _).1 (x : Wb X).2
  have hUb := (mem_Ub X u _).1 x.2
  have hw0 : w ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext (Subtype.ext h)
  have h1 : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) w = 0 := by
    intro a
    change (VS D).hT w ((X.Fu u).fvec a) = 0
    induction a using Fin.lastCases with
    | last =>
      rw [FlagG.fvec, Fin.snoc_last, X.flagZVector]
      exact p_symm_zero (VS D) hUb
    | cast b =>
      rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
      exact p_symm_zero (VS D) (hWb b).1
  have h2 : w ∉ (GlobalTheory.TypeAsm.F0 X u).X := by
    intro hX
    apply hw0
    refine eq_zero_of_mem_span_eX X w ?_ (fun b => (hWb b).2)
    refine (Submodule.span_le.2 ?_) hX
    rintro _ ⟨b, -, rfl⟩
    change (X.Fu u).fvec b.castSucc ∈ _
    rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
    exact Submodule.subset_span ⟨b, rfl⟩
  have := hpos w h1 h2
  rw [hU_apply]
  exact this

end GlobalTheory.RowsOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseNormalFormRealFramesAtRealPlaces
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.BaseFrame

theorem normal0_one (k r j : ℕ) (hj : j ≤ r) (h0 : j = 0) (z : Fin (2 * r + k + 1) → ℂ) :
    GlobalTheory.Amp.IsNormal0 k r hj (fun _ => 0) 1 z z 1 := by
  subst h0
  refine ⟨?_, by simp, by simp, monotone_const, fun a b _ => by simp, fun a ha => absurd ha (Nat.not_lt_zero _),
    fun a _ => by simp, ?_⟩
  · show (1 : Matrix _ _ ℂ)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  · refine ⟨monotone_const, ?_, fun a => a.elim0, fun a => a.elim0⟩
    simp [Matrix.det_fin_zero]

end GlobalTheory.TypeAsm.BaseFrame

open GlobalTheory.TypeAsm.BaseFrame in
theorem GlobalTheory.TypeAsm.baseFrame_real : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u → N.j = 0 → N.T = Tu D u → N.ist = X.fY →
      ∀ τ : D.what₂.Tau, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) (fun _ => 0)
        (phiV C τ) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) 1 := by
  intro D large₂ X u C hStd N hF hF' hj hT hist τ
  have hv : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := (GlobalTheory.TypeAsm.hostC D large₂ hStd).2.2.1
  rw [hv]
  have hFe : ∀ a : Fin D.R.rS, (F0 X u).e a.castSucc = X.eX a := by
    intro a
    show (lf D (X.Fu u)).fl.fvec a.castSucc = X.eX a
    rw [fv_cast]
    exact congrFun (X.Fu_e u) a
  have hFz : (F0 X u).z = X.zu u := by
    show (lf D (X.Fu u)).fl.fvec (Fin.last _) = X.zu u
    rw [fv_last]
    exact X.flagZVector u
  have hpe : ∀ a : Fin D.R.rS, phiV C τ (X.eX a) =
      (((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) :=
    fun a => GlobalTheory.CovDom.ModelIso.qi_e X C τ a
  have hpf : ∀ a : Fin D.R.rS, phiV C τ (X.fY a) =
      ((((2 * D.host.v) ^ (D.R.rS - (a : ℕ)) : ℝ) : ℂ))⁻¹ • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) :=
    fun a => GlobalTheory.CovDom.ModelIso.qi_f X C τ a
  have hpz : phiV C τ (X.zu u) = zB X (C.Qi τ) u τ := rfl
  obtain ⟨hzW, hzT⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hTz : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hzT]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  refine ⟨⟨GlobalTheory.TypeAsm.GramPf.phiV_add C τ, GlobalTheory.TypeAsm.GramPf.phiV_smul C τ, GlobalTheory.TypeAsm.GramPf.phiV_herm C τ,
    GlobalTheory.TypeAsm.GramPf.phiV_span C τ⟩, hzW, hzW, hTz, ⟨1, normal0_one _ _ _ N.j_le hj _⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hF, hF', hFe, Matrix.one_mulVec, hpe]
    exact ⟨rfl, rfl⟩
  · intro b _
    rw [hist, hpf]
    push_cast
    rfl
  · rw [hF, hFz, hpz]
  · rw [hF', hFz, Matrix.one_mulVec, hpz]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelHyperbolicBasisScaled
section
noncomputable section
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm.FramePf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ka_div (D : D7) : D.host.ka / (2 * Real.pi) = (2 * D.host.v)⁻¹ := by
  have h0 : 0 < D.host.rdE := GlobalTheory.TypeAsm.GramPf.rdE_pos' D
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
  field_simp

theorem two_v_pos (D : D7) : 0 < 2 * D.host.v := by
  have h0 : 0 < D.host.rdE := GlobalTheory.TypeAsm.GramPf.rdE_pos' D
  simp only [Formalism.BasicNotions.Host.v]
  linarith

theorem phiV_frame (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    GlobalTheory.TypeAsm.phiV C τ (X.eX a) =
                 (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) ∧
    GlobalTheory.TypeAsm.phiV C τ (X.fY a) =
                 ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨hQiQ, _, _, hfr⟩ := C.isT τ
  obtain ⟨h1, h2⟩ := hfr a a rfl
  have hc : ((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) ≠ 0 := pow_ne_zero _ (two_v_pos D).ne'
  have hfp : frS D ^ (D.R.rS - a.val) = ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) := by
    unfold frS
    rw [ka_div, ← Complex.ofReal_pow, inv_pow]
  unfold GlobalTheory.TypeAsm.phiV
  constructor
  · have e : rv X.B.I (vOf X τ) (X.crd (X.eX a)) =
        ((((2 * D.host.v) ^ (D.R.rS - a.val)) : ℝ) : ℂ) • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
      rw [h1, hfp, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc, Complex.ofReal_one, one_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
    rfl
  · have e : rv X.B.I (vOf X τ) (X.crd (X.fY a)) =
        ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
      rw [h2, hfp, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_inv, inv_inv, smul_smul,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hc, Complex.ofReal_one, one_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
    rfl

end GlobalTheory.TypeAsm.FramePf
end
end

