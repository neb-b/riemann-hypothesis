module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0638
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0332
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDetParabolicFrameStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_det_parabolic_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ (p : G2 σ Y) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsPar p t → bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hb p).1 = Matrix.GeneralLinearGroup.det t := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrameDet.bdet_frameEquiv | exact GlobalTheory.CompanionTheory.SiegelFrameDet.bdet_frameEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelFrameDet.bdet_frameEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeToCohomologyIsoStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_hodge_to_cohomology_iso : ∀ (R : Type) [CommRing R], ∃ e : ∀ {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ a : ℕ,
    (∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) → ∀ j : ℕ,
      CH.H F (a + j) ≃ₗ[R] (cechH F U a).cx.H j,
    ∀ {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type}
      (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T)
      (hU' : ∀ α, Cosieve (U' α)) (hc' : ∀ T, ∃ α, U' α T) (a : ℕ)
      (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r))
      (hv' : ∀ n (i : Fin (n + 1) → ι') r, r ≠ a → Subsingleton (HU F' (capT U' i) r)) (m : CH.Mor F F' (RingHom.id R))
      (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (j : ℕ) (c : (cechH F U a).X j)
      (h0 : (cechH F U a).cx.d j c = 0)
      (h1 : (cechH F' U' a).cx.d j (fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      m.pull (a + j) ((e F U hU hc a hv j).symm ((cechH F U a).cx.cls c h0)) =
        (e F' U' hU' hc' a hv' j).symm ((cechH F' U' a).cx.cls _ h1) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.cech_deg | exact GlobalTheory.CompanionTheory.CechSerre.cech_deg | (intros; apply GlobalTheory.CompanionTheory.CechSerre.cech_deg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellConditionsOfSmulEq
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem isIdem_mul_self_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) : e * e = e := by
  have h : e * e - e = 0 := by
    refine GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)
    · rw [RingHom.map_sub, RingHom.map_mul, he.1 w, mul_one, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, he.2 v]
      split_ifs
      · rw [mul_one, sub_self]
      · rw [mul_zero, sub_self]
  exact sub_eq_zero.1 h

theorem entry_sub_one_of_bc {B : Type} [CommRing B] (φ : AE D →+* B) {u : G D p}
    (h : Formalism.UG.bc φ (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig (Jst D p) u) = 1)
    (i j : Fin (p + p)) : φ ((mat u - 1) i j) = 0 := by
  have h1 : φ.mapMatrix (mat u) = 1 := congrArg Units.val h
  have h2 : φ.mapMatrix (mat u - 1) = 0 := by
    rw [map_sub, h1, map_one, sub_self]
  exact congrFun (congrFun h2 i) j

theorem smul_mat_sub_one_eq_zero {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {u : G D p}
    (hu : u ∈ KOff D p S) : e • (mat u - 1) = 0 := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.AdelicU.mem_levelOff.1 hu
  have h1' := GlobalTheory.AdelicU.mem_finPts_iff_forall.1 h1
  ext i j
  change e * (mat u - 1) i j = 0
  refine GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D _ (fun w => ?_) (fun v => ?_)
  · have hb := GlobalTheory.AdelicU.matHom_projArch D.sp.cm.sig (Jst D p) w u
    rw [h1' w, map_one] at hb
    rw [RingHom.map_mul, entry_sub_one_of_bc _ (Units.ext (congrArg Units.val hb.symm)) i j, mul_zero]
  · rw [RingHom.map_mul, he.2 v]
    split_ifs with hv
    · have hb := GlobalTheory.AdelicU.matHom_proj D.sp.cm.sig (Jst D p) v u
      rw [h2 v hv, map_one] at hb
      have hc : cv D v ((mat u - 1) i j) = 0 :=
        entry_sub_one_of_bc _ (Units.ext (congrArg Units.val hb.symm)) i j
      rw [hc, mul_zero]
    · rw [zero_mul]

theorem smul_mat_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • mat (g * u) = e • mat g := by
  have h1 : e • mat u = e • (1 : Mx D (p + p) (p + p)) := by
    have := smul_mat_sub_one_eq_zero he hu
    rwa [smul_sub, sub_eq_zero] at this
  have h2 : mat (g * u) = mat g * mat u := rfl
  rw [h2, ← Matrix.mul_smul, h1, Matrix.mul_smul, mul_one]

theorem smul_lowC_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • lowC (g * u) = e • lowC g := by
  have h := smul_mat_mul_right he g hu
  ext i j
  exact congrFun (congrFun h _) _

theorem smul_lowD_mul_right {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (g : G D p) {u : G D p}
    (hu : u ∈ KOff D p S) : e • lowD (g * u) = e • lowD g := by
  have h := smul_mat_mul_right he g hu
  ext i j
  exact congrFun (congrFun h _) _

theorem cell_conditions_of_smul_eq {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] {e : R}
    (hee : e * e = e) {c c' d d' x y : Matrix n n R} (hc : e • c' = e • c) (hd : e • d' = e • d)
    (hxe : e • x = x) (hy : y * c = e • (1 : Matrix n n R)) (hx : c * x = e • d) :
    (e • y) * c' = e • (1 : Matrix n n R) ∧ c' * x = e • d' := by
  constructor
  · rw [Matrix.smul_mul, ← Matrix.mul_smul, hc, Matrix.mul_smul, hy, smul_smul, hee]
  · calc c' * x = c' * (e • x) := by rw [hxe]
      _ = (e • c') * x := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (e • c) * x := by rw [hc]
      _ = c * (e • x) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = c * x := by rw [hxe]
      _ = e • d := hx
      _ = e • d' := hd.symm

theorem isB_of_smul_eq {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {g g' : G D p}
    (hc : e • lowC g' = e • lowC g) (hd : e • lowD g' = e • lowD g) (x : hermS D p e)
    (h : IsB e g x) : IsB e g' x := by
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  have hxe : e • x.1.1 = x.1.1 := x.2
  obtain ⟨h1, h2⟩ := cell_conditions_of_smul_eq (isIdem_mul_self_right he) hc hd hxe hy hx
  exact ⟨⟨e • y, h1⟩, h2⟩

theorem isB_mul_right_iff {D : D7} {p : ℕ} {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    {g u : G D p} (hu : u ∈ KOff D p S) (x : hermS D p e) : IsB e (g * u) x ↔ IsB e g x :=
  ⟨isB_of_smul_eq he (smul_lowC_mul_right he g hu).symm (smul_lowD_mul_right he g hu).symm x,
    isB_of_smul_eq he (smul_lowC_mul_right he g hu) (smul_lowD_mul_right he g hu) x⟩

end GlobalTheory.CompanionTheory.MuC

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermCofiniteIdealTransfer
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1

theorem slice_mem_genSpace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₁ : Set (Module.End ℂ (Sm E r)), Cofin J₁ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₁ : Subgroup (GL (Fin r) (Af E))) (ρ₁ : Representation ℂ (Kinf E r) W), IsOpen (L₁ : Set (GL (Fin r) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₁ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₂ : GA E s, ∃ G ∈ genSpace L₁ ρ₁ J₁, ∀ m₁ : GA E r, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  intro E _ _ _ r s L hL W _ _ _ ρ hρ J hJ J₁ hJ₁ H3 t κ
  refine ⟨levelOne s L t, ρ.comp (levK E r s), isOpen_levelOne hL t,
    fun ℓ w => (hρ ℓ w).comp continuous_levK, ?_⟩
  intro F hF m₂
  obtain ⟨hN, hM, hLv, hC, hG, hZ⟩ := hF
  let h : GA E (r + s) := lev (Ad E) r s (1, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)
  let F' := rt E (r + s) h F
  let G : Sm E r := ⟨_, GlobalTheory.T.levi_restriction_smooth E r s F'.1 F'.2⟩
  have hGv : ∀ m₁, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
    intro m₁
    change F.1 (lev (Ad E) r s (m₁, 1) * h) = _
    have e : (m₁, m₂) = ((m₁, 1) * (1, m₂) : GA E r × GA E s) := by simp
    rw [e, map_mul]
    simp only [h, mul_assoc]

  have hcoef : ∀ g : GA E r, (fun k : Kinf E r => (cptRep E r k G).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (levK E r s)) := by
    intro g
    have key := coeff_comp ρ (levK E r s) κ (hC (lev (Ad E) r s (g, m₂) * finGL E (r + s) t))
    convert key using 1
    funext k
    change G.1 (g * infGL E r (Unitary.toUnits k)) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
      infGL E (r + s) (Unitary.toUnits (levK E r s k * κ)))
    rw [hGv, lev_infGL_right, ← toUnits_levK (s := s),
      ← map_mul (Unitary.toUnits : _ →* (Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))ˣ)]

  have hle : (levelOne s L t : Set (GL (Fin r) (Af E))) ⊆ {k | finRep E r k G = G} := by
    intro k hk
    refine Subtype.ext (funext fun m => ?_)
    change G.1 (m * finGL E r k) = G.1 m
    rw [hGv, hGv]
    have hk' : F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t)) =
        F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) :=
      congrFun (congrArg Subtype.val (hLv _ (mem_levelOne.1 hk))) _
    rw [← hk', lev_finGL_right]

  have hkill : ∀ z ∈ J₁, z G = 0 := by
    refine H3 F' (fun x g => ?_) (fun z hz => ?_) G (fun m => rfl)
    · change F.1 (unip x * g * h) = F.1 (g * h)
      rw [mul_assoc, hN]
    · change z (rt E (r + s) h F) = 0
      rw [← Module.End.mul_apply, (commute_rt_of_mem_Zalg (hJ.1 hz) h).eq, Module.End.mul_apply, hZ z hz, map_zero]
  refine ⟨G, ⟨⟨fun γ g => ?_, isOpen_stab_of_mem_nhds (finRep E r) G
      (Filter.mem_of_superset ((isOpen_levelOne hL t).mem_nhds (one_mem _)) hle),
    kfin_of_coeff _ G hcoef, zfin_of_cofin hJ₁ hkill, fun g => ?_⟩, fun k hk => hle hk, hcoef, hkill⟩, hGv⟩
  ·
    rw [hGv, hGv]
    have e : lev (Ad E) r s (ratGL E r γ * g, m₂) = lev (Ad E) r s (ratGL E r γ, ratGL E s 1) * lev (Ad E) r s (g, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul]
    simp only [e, mul_assoc]
    exact hM (γ, 1) _
  ·
    obtain ⟨C, N, hb⟩ := hG (lev (Ad E) r s (g, m₂) * finGL E (r + s) t)
    obtain ⟨B, hB0, hB⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le E r s (Unitary.toUnits κ)
    refine ⟨|C| * B ^ N, N, fun y => ?_⟩
    have e1 : G.1 (g * infGL E r y) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
        infGL E (r + s) (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)) := by
      rw [hGv, lev_infGL_right]
    rw [e1]
    have h1 := hb (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)
    have h2 := hB y
    have h0 : 0 ≤ height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) := zero_le_one.trans (one_le_height _)
    calc _ ≤ C * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N := h1
      _ ≤ |C| * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)
      _ ≤ |C| * (B * height y) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 N) (abs_nonneg C)
      _ = |C| * B ^ N * height y ^ N := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnipotentBlockFamily
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem continuous_unipotent_block_family {X R : Type} [TopologicalSpace X] [TopologicalSpace R] [Zero R] [One R] {n : ℕ}
    {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) :
    Continuous fun x => blk4 (1 : Matrix (Fin n) (Fin n) R) (f x) 0 1 := by
  unfold blk4
  exact (continuous_const.matrix_fromBlocks hf continuous_const continuous_const).matrix_submatrix _ _

theorem unipotent_block_mul_add {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) :
    blk4 (1 : Matrix (Fin n) (Fin n) R) b 0 1 * blk4 1 c 0 1 = blk4 1 (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem continuous_nb {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) : Continuous nb := by
  have emb := isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D p)
  rw [emb.continuous_iff, Units.continuous_iff]
  have hv : Continuous fun b : hermA D p => (b.1 : Mx D p p) := continuous_subtype_val
  have hm : ∀ b, (AdelicU.matHom _ D.sp.cm.sig (Jst D p) (nb b)).1 = blk4 1 b.1 0 1 := hnb
  constructor
  · refine (continuous_unipotent_block_family hv).congr fun b => ?_
    exact (hm b).symm
  · refine (continuous_unipotent_block_family hv.neg).congr fun b => ?_
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp only [Function.comp]
    rw [hm b, unipotent_block_mul_add]
    simp [blk4]

end GlobalTheory.CompanionTheory.MuC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGeneric
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GenSwap

open GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

theorem isGenericFor_prodIrr (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) (hC : GlobalTheory.BZSeg.CuspGeneric k)
    {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hc : ∀ a, (x a).IsCusp) (hd : ∑ a, (x a).1 = N) : IsGenericFor ψ (prodIrr x hd) := by
  rw [← isGeneric_iff_isGenericFor hψ h1]
  exact (GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity k hW h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)).2 fun a =>
      hC _ _ _ (hc a).1 (x a).2.rep.smooth (x a).2.rep.irr (hc a).2

theorem isSubquotient_of_generic_common {N : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) {U V V' W : Type}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (T : Representation ℂ (GL (Fin N) k) U) (P : Representation ℂ (GL (Fin N) k) V)
    (P' : Representation ℂ (GL (Fin N) k) V') (hT : IsSubquotient T P) (hT' : IsSubquotient T P')
    (hTg : IsGenericFor ψ T) (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTs : IsSmooth T := hT.isSmooth hP
  have hTf : GlobalTheory.SmGL.HasFiniteLength T := GlobalTheory.CompanionTheory.IrrSub.hasFiniteLength_of_isSubquotient hT hfl
  obtain ⟨A, B, -, hi', -, hg'⟩ := _root_.GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot k ψ hψ N T hTs hTf hTg
  have s₁ := GlobalTheory.ParIndExact.isSubquotient_subQuot A B
  obtain ⟨e⟩ := GlobalTheory.T.whittaker_rank_extension_bound k ψ hψ N P σ (subQuot A B) hP hr hi hi' hsq (s₁.trans hT) hgσ hg'
  exact isSubquotient_of_equiv_left e.symm (s₁.trans hT')

theorem isSubquotient_of_common {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y Z : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Z a)) (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a))
    (hτ : ∀ a, IsSmooth (τ a)) (hq : ∀ a, IsSubquotient (τ a) (π a)) (hq' : ∀ a, IsSubquotient (τ a) (π' a))
    (hg : ∀ a, IsGenericFor ψ (τ a)) {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTg : IsGenericFor ψ (multiProd (stdBlocks d hN) τ) := by
    obtain ⟨H⟩ := hW ψ hψ h1 s N d hN Z τ hτ
    have : Nontrivial (⨂[ℂ] a, TwJacquet (τ a) (unipB k (Fin (d a))) (whitChar ψ (d a))) :=
      (GlobalTheory.CompanionTheory.Leib.nontrivial_piTensorProduct_iff _).2 hg
    exact H.toEquiv.nontrivial
  exact isSubquotient_of_generic_common hψ _ P P'
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z X τ π hπ hq) E)
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z Y τ π' hπ' hq') E') hTg hP hfl hr σ hi hgσ hsq

theorem isSubquotient_of_positions {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a)) (hg : ∀ a, IsGenericFor ψ (π a))
    (hf : ∀ a, GlobalTheory.SmGL.HasFiniteLength (π a))
    (hsw : ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (π a) → IsSubquotient g (π' a))
    {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have ex := fun a => _root_.GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot k ψ hψ (d a) (π a) (hπ a) (hf a) (hg a)
  choose A B _ hirr hsm hgen using ex
  have hq : ∀ a, IsSubquotient (subQuot (A a) (B a)) (π a) := fun a => GlobalTheory.ParIndExact.isSubquotient_subQuot _ _
  exact isSubquotient_of_common hW hψ h1 d hN π π' (fun a => subQuot (A a) (B a)) hπ hπ' hsm hq
    (fun a => hsw a _ _ (hsm a) (hirr a) (hq a)) hgen P P' E E' hP hfl hr σ hi hgσ hsq

theorem fac_rev {h j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k)) (i : Fin 2) :
    (fac hj x 1 : Fin 2 → IrrGL (k := k)) (Fin.rev i) = (fac' hj x 1 : Fin 2 → IrrGL (k := k)) i := by
  rw [fac_one hj x, fac'_one hj x]
  fin_cases i <;> rfl

theorem nonempty_equiv_of_eq {n M : ℕ} {u v : Fin n → IrrGL (k := k)} (e : u = v) (h₁ : ∑ a, (u a).1 = M)
    (h₂ : ∑ a, (v a).1 = M) : Nonempty ((prodIrr u h₁).Equiv (prodIrr v h₂)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩


set_option maxHeartbeats 1000000 in
theorem position_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) {h j : ℕ} (hj : j + 1 < h)
    (x : Fin h → IrrGL (k := k)) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) :
    ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (prodIrr (fac hj x a) (s₁ a)) →
      IsSubquotient g (prodIrr (fac' hj x a) (s₂ a)) := by
  refine fin_three_forall ?_ ?_ ?_
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_zero hj x).symm (s₁ 0) (s₂ 0)
    exact isSubquotient_of_equiv hq E
  · intro W _ _ g hgs hgi hq
    have hd2 : ∑ a, (fac hj x 1 (Fin.rev a)).1 = d 1 :=
      (Equiv.sum_comp Fin.revPerm fun b => (fac hj x 1 b).1).trans (s₁ 1)
    obtain ⟨E⟩ := prodIrr_congr rfl (fun a => fac hj x 1 (Fin.rev a)) (fac' hj x 1) (fun i => fac_rev hj x i) hd2 (s₂ 1)
    exact isSubquotient_of_equiv (GlobalTheory.T.reversed_product_same_subquotients hA hGK (fac hj x 1) (s₁ 1) hd2 g hgs hgi hq) E
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_two hj x).symm (s₁ 2) (s₂ 2)
    exact isSubquotient_of_equiv hq E


set_option maxHeartbeats 1000000 in
theorem core (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) (hW : GlobalTheory.BZMir.Leib.WhitHeredity k)
    (hR : GlobalTheory.BZSeg.WhitRankIrr k) (hC : GlobalTheory.BZSeg.CuspGeneric k) (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) {h N j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k)) (hc : ∀ a, (x a).IsCusp) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) (hN : ∑ a, d a = N)
    (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible)
    (hg : IsGenericFor ψ σ) (hsq : IsSubquotient σ (prodIrr x hd)) :
    IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  have hJ : j < h := by omega
  have hkey : ∀ c, fac' hj x (ofLex (order hj c)).1 (ofLex (order hj c)).2 =
      x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ c) := fun c =>
    congrArg (fun y => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ y)) (place_order hj c)
  obtain ⟨p⟩ := flatten (grp h j) (fac hj x) d s₁ hN (order hj) x (fun c => congrArg x (place_order hj c)) hd
  obtain ⟨q⟩ := flatten (grp h j) (fac' hj x) d s₂ hN (order hj)
    (fun a => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ a)) hkey hd'
  exact isSubquotient_of_positions hW hψ h1 d hN (fun a => prodIrr (fac hj x a) (s₁ a))
    (fun a => prodIrr (fac' hj x a) (s₂ a)) (fun _ => isSmooth_prodIrr _ _) (fun _ => isSmooth_prodIrr _ _)
    (fun a => isGenericFor_prodIrr hW hC hψ h1 _ (fun _ => hc _) _) (fun _ => GlobalTheory.T.product_irreducible_finite_length hA _ _)
    (position_swap hA hGK hj x d s₁ s₂) _ _ p q
    (isSmooth_prodIrr _ _) (GlobalTheory.T.product_irreducible_finite_length hA _ _) (GlobalTheory.T.whittaker_rank_product_le_one k hW hR ψ hψ h1 h N x hd) σ hi hg hsq

theorem isSubquotient_prodIrr_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  intro k _ _ _ _ hA hGK hW hR hC ψ hψ h1 h N x hc hd j hj hd' W _ _ σ _ hi hg hsq
  have t : ∑ b : Fin 2, ((fac' hj x 1 : Fin 2 → IrrGL (k := k)) b).1 = ∑ b : Fin 2, ((fac hj x 1 : Fin 2 → IrrGL (k := k)) b).1 := by
    rw [fac_one hj x, fac'_one hj x]
    simp [Fin.sum_univ_two, add_comm]
  have s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = ∑ b, (fac hj x a b).1 :=
    fin_three_forall (by rw [fac'_zero hj x]) t (by rw [fac'_two hj x])
  exact core hA hGK hW hR hC ψ hψ h1 hj x hc (fun a => ∑ b, (fac hj x a b).1) (fun _ => rfl) s₂
    ((sum_place hj fun c => (x c).1).trans hd) hd hd' σ hi hg hsq

end GlobalTheory.CompanionTheory.GenSwap

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvarianceStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_K_invariance : PositivityTheory.PfSWUS.HeightKInv := by
  first | exact @GlobalTheory.CompanionTheory.PfSWUS.height_mul_K | exact GlobalTheory.CompanionTheory.PfSWUS.height_mul_K | (intros; apply GlobalTheory.CompanionTheory.PfSWUS.height_mul_K <;> assumption)
end
end

