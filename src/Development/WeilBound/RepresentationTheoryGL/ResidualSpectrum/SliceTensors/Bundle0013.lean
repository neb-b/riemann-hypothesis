module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapC
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

namespace C

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

theorem hsum (r s : ℕ) : ∑ i, ![r, s] i = r + s := by simp [Fin.sum_univ_two]

abbrev eC (r s : ℕ) : (Σ i, Fin (![r, s] i)) ≃ Fin (r + s) := GlobalTheory.SmGL.stdBlocks ![r, s] (hsum r s)

theorem eC_zero (i : Fin r) : eC r s ⟨0, i⟩ = Fin.castAdd s i :=
  Fin.ext ((GlobalTheory.SmGL.stdBlocks_val ![r, s] (hsum r s) 0 i).trans (by simp))

theorem eC_one (j : Fin s) : eC r s ⟨1, j⟩ = Fin.natAdd r j :=
  Fin.ext ((GlobalTheory.SmGL.stdBlocks_val ![r, s] (hsum r s) 1 j).trans (by simp))

theorem lowLeft {p : GL (Fin (r + s)) (Cinf E)} (hp : p ∈ parab (Cinf E) (eC r s)) :
    ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (p : Matrix _ _ (Cinf E)) i j = 0 := by
  intro i j hi hj
  have h := GlobalTheory.SmGL.mem_parab_iff.1 hp 1 0 (show Fin s from ⟨i - r, by omega⟩) (show Fin r from ⟨j, hj⟩)
    (by decide)
  rw [eC_one, eC_zero] at h
  convert h using 2 <;> apply Fin.ext <;> simp; omega

theorem decomp (p : parab (Cinf E) (eC r s)) :
    ∃ (u : BlockIx (r + s) r → Cinf E) (m : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)),
      p.1 = unip u * lev (Cinf E) r s m :=
  IwaFin.exists_unip_mul_lev r s p.1 (lowLeft p.2) (lowLeft (inv_mem p.2))

theorem contDiff_cc : ContDiff ℝ ∞ fun M : Lie E (r + s) => (fun i j => M (Fin.castAdd s i) (Fin.castAdd s j) : Lie E r) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ (fun _ : Fin (r + s) => Cinf E) (Fin.castAdd s j)).comp
      (contDiff_apply ℝ (fun _ : Fin (r + s) => Fin (r + s) → Cinf E) (Fin.castAdd s i))

theorem contDiff_nn : ContDiff ℝ ∞ fun M : Lie E (r + s) => (fun i j => M (Fin.natAdd r i) (Fin.natAdd r j) : Lie E s) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
    (contDiff_apply ℝ (fun _ : Fin (r + s) => Cinf E) (Fin.natAdd r j)).comp
      (contDiff_apply ℝ (fun _ : Fin (r + s) => Fin (r + s) → Cinf E) (Fin.natAdd r i))

end C

open C in
theorem exists_local (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) :
    ∃ (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E)) (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E))
      (κ : Lie E (r + s) → Kinf E (r + s)) (u : Lie E (r + s) → BlockIx (r + s) r → Cinf E),
      ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (κ y).1) (oneL E (r + s)) ∧
      b₁ (oneL E (r + s)) = 1 ∧ b₂ (oneL E (r + s)) = 1 ∧ κ (oneL E (r + s)) = 1 ∧
      ∀ᶠ y in nhds (oneL E (r + s)), Matrix.of y = (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1 := by
  obtain ⟨p, k, hp, hk, hp1, hk1, hpk⟩ := GlobalTheory.SmoothIwasawaNear.exists_local_iwasawa E ![r, s] (eC r s)
  choose u m hm using fun y => decomp (E := E) (p y)
  have e1 : ∀ y, toL (m y).1.val = (fun i j => toL (p y).1.val (Fin.castAdd s i) (Fin.castAdd s j) : Lie E r) :=
    fun y => by
      funext i j
      change ((m y).1 : Matrix _ _ (Cinf E)) i j = ((p y).1 : Matrix _ _ (Cinf E)) (Fin.castAdd s i) (Fin.castAdd s j)
      rw [hm y, unip_lev_cc]
  have e2 : ∀ y, toL (m y).2.val = (fun i j => toL (p y).1.val (Fin.natAdd r i) (Fin.natAdd r j) : Lie E s) :=
    fun y => by
      funext i j
      change ((m y).2 : Matrix _ _ (Cinf E)) i j = ((p y).1 : Matrix _ _ (Cinf E)) (Fin.natAdd r i) (Fin.natAdd r j)
      rw [hm y, unip_lev_nn]
  refine ⟨fun y => (m y).1, fun y => (m y).2, k, u, ?_, ?_, hk, ?_, ?_, hk1, ?_⟩
  · simp only [e1]
    exact contDiff_cc.contDiffAt.comp _ hp
  · simp only [e2]
    exact contDiff_nn.contDiffAt.comp _ hp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun (e1 (oneL E (r + s))) i) j
    change ((m _).1 : Matrix _ _ (Cinf E)) i j = _ at this
    rw [this, hp1]
    simp [Matrix.one_apply, Fin.castAdd_inj]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun (e2 (oneL E (r + s))) i) j
    change ((m _).2 : Matrix _ _ (Cinf E)) i j = _ at this
    rw [this, hp1]
    simp [Matrix.one_apply, Fin.natAdd_inj]
  · filter_upwards [hpk] with y hy
    rw [hy, hm y]

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PLocDual
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc Zc.Cos

namespace PositivityTheory.Rg.Rs

namespace PLocDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem basis (N : ℕ) : ∀ U ∈ nhds (1 : GL (Fin N) k), ∃ K : Subgroup (GL (Fin N) k),
    IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) ∧ (K : Set (GL (Fin N) k)) ⊆ U :=
  fun U hU => by
    obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin N) U hU
    exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem contraMap_surjective {N : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {σ : Representation ℂ (GL (Fin N) k) X} {τ : Representation ℂ (GL (Fin N) k) Y} (hσ : IsSmooth σ)
    (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ) (hf : Function.Injective f) :
    Function.Surjective (GlobalTheory.ContraRefl.contraMap f) := by
  intro l
  obtain ⟨K, ho, hc, hKs⟩ := basis N _ ((isSmooth_contra σ l).mem_nhds (by simp))
  have hlK : l ∈ fixed (contra σ) K := GlobalTheory.ContraRefl.mem_fix.2 fun h hh => hKs hh
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f.toLinearMap (LinearMap.ker_eq_bot.2 hf)
  obtain ⟨l', h1, h2⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hτ ho hc
    (((l : Module.Dual ℂ X) ∘ₗ g) ∘ₗ (fixed τ K).subtype)
  have hl'K : l' ∈ fixed (contra τ) K := GlobalTheory.ContraRefl.mem_fix.2 h1
  refine ⟨l', Subtype.ext (GlobalTheory.ContraRefl.form_ext hσ hc (fun h hh w => ?_) (fun h hh w => ?_) fun w hw => ?_)⟩
  · show (l' : Module.Dual ℂ Y) (f (σ h w)) = (l' : Module.Dual ℂ Y) (f w)
    rw [f.isIntertwining]
    exact GlobalTheory.ContraRefl.invariant_of_fixed ⟨l', hl'K⟩ h hh (f w)
  · exact GlobalTheory.ContraRefl.invariant_of_fixed ⟨l, hlK⟩ h hh w
  · have hfw : f w ∈ fixed τ K := GlobalTheory.ContraRefl.mem_fix.2 fun h hh => by
      rw [← f.isIntertwining]
      exact congrArg f (GlobalTheory.ContraRefl.mem_fix.1 hw h hh)
    show (l' : Module.Dual ℂ Y) (f w) = (l : Module.Dual ℂ X) w
    have e1 := h2 ⟨f w, hfw⟩
    have e2 := LinearMap.congr_fun hg w
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e2
    rw [show f w = ((⟨f w, hfw⟩ : fixed τ K) : Y) from rfl, e1]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg _ e2

def untwist {N : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {π : Representation ℂ (GL (Fin N) k) X} {σ : Representation ℂ (GL (Fin N) k) Y}
    (q : π.IntertwiningMap (σ.comp (thetaW k N))) : Representation.IntertwiningMap (π.comp (thetaW k N)) σ where
  toLinearMap := q.toLinearMap
  isIntertwining' g := by
    ext x
    have h := q.isIntertwining _ _ (thetaW k N g) x
    simp only [MonoidHom.comp_apply, GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW] at h
    exact h

theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩


set_option maxHeartbeats 2000000 in
theorem exists_surjective_rev {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N)
    (σ : GlobalTheory.CuspRep.SmIrr (GL (Fin N) k)) (f : σ.ρ.IntertwiningMap (prodIrr x hd)) (hf : f ≠ 0) :
    ∃ hd' : ∑ a, (x (Fin.rev a)).1 = N,
      ∃ g : (prodIrr (fun a => x (Fin.rev a)) hd').IntertwiningMap σ.ρ, Function.Surjective g := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have hGK : GKLocal k := GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA
  have hinj : Function.Injective f := GlobalTheory.DiscreteSpectrumCM.injective_of_irreducible σ.irred f fun e =>
    hf (Representation.IntertwiningMap.ext e)
  obtain ⟨hd1, ⟨E1⟩⟩ := GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr hA x hd
  have hs := contraMap_surjective σ.smooth (isSmooth_prodIrr x hd) f hinj
  obtain ⟨E2⟩ := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra hGK N σ.ρ σ.smooth σ.irred
  let q : (prodIrr (fun a => dualCl (x a)) hd1).IntertwiningMap (σ.ρ.comp (thetaW k N)) :=
    (E2.symm.toIntertwiningMap.comp (GlobalTheory.ContraRefl.contraMap f)).comp E1.symm.toIntertwiningMap
  have hq : Function.Surjective q :=
    E2.symm.toLinearEquiv.surjective.comp (hs.comp E1.symm.toLinearEquiv.surjective)
  obtain ⟨hd2, ⟨E3⟩⟩ := GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW hA hGK (fun a => dualCl (x a)) hd1
  have e : (fun a => dualCl (dualCl (x (Fin.rev a)))) = fun a => x (Fin.rev a) :=
    funext fun a => GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA _
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hd]; exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  obtain ⟨E4⟩ := prodIrr_congr e hd2 hd'
  exact ⟨hd', ((untwist q).comp E3.symm.toIntertwiningMap).comp E4.symm.toIntertwiningMap,
    (hq.comp E3.symm.toLinearEquiv.surjective).comp E4.symm.toLinearEquiv.surjective⟩

end PLocDual

set_option maxHeartbeats 2000000 in
open PLocDual in
theorem locDual_holds : LocDual := by
  intro k _ _ _ _ _ N d x σ' _ _ hd f hf
  obtain ⟨hd', g, hg⟩ := exists_surjective_rev (fun i : Fin d => spehFactor x d i.rev) hd σ' f hf
  have e : (fun a : Fin d => spehFactor x d (Fin.rev (Fin.rev a))) = spehFactor x d :=
    funext fun a => by rw [Fin.rev_rev]
  have hd'' : ∑ i, (spehFactor x d i).1 = N := by simpa only [Fin.rev_rev] using hd'
  obtain ⟨E⟩ := prodIrr_congr e hd' hd''
  exact ⟨hd'', g.comp E.symm.toIntertwiningMap, hg.comp E.symm.toLinearEquiv.surjective⟩

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesC
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.InductionInStages

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d N : ℕ}

theorem tw_unip_inv {h : ∑ _ : Fin d, a = N} {fam : Fin d → CuspSub E a} {z : ℂ} {F : Sm E N}
    (hF : F ∈ tw (indForms h fam) z) : ∀ u ∈ unipRad (Ad E) (stdBlocks (fun _ : Fin d => a) h), ∀ g, F.1 (u * g) = F.1 g := by
  obtain ⟨G, hG, rfl⟩ := hF
  intro u hu g
  have h1 : chiDet N (Model.absC E z) u = 1 := by
    simp only [chiDet, MonoidHom.comp_apply, det_eq_one_of_mem_unipRad (Ad E) hu, map_one]
  change (mulChi N (Model.absC E z) G).1 (u * g) = (mulChi N (Model.absC E z) G).1 g
  rw [mulChi_apply, mulChi_apply, hG.1 u hu g, map_mul, h1, one_mul]

theorem tw_slice_mem {h : ∑ _ : Fin d, a = N} {fam : Fin d → CuspSub E a} {z : ℂ} {F : Sm E N}
    (hF : F ∈ tw (indForms h fam) z) :
    (fun m : Fin d → GA E a => F.1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d => a) h) m)) ∈
      tensorForms (n := fun _ => a) (fun b => (fam b).twist (Model.absC E z)) := by
  obtain ⟨G, hG, rfl⟩ := hF
  have h1 := tensorForms_mulChi fam (Model.absC E z) (hG.2.2.2 1 1)
  convert h1 using 1
  funext m
  change (mulChi N (Model.absC E z) G).1 _ = _
  rw [mulChi_apply, chiDet_leviEmb]
  simp

variable {r s d₁ d₂ : ℕ}

theorem mem_indForms_of_slices (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    {fam₁ : Fin d₁ → CuspSub E a} {fam₂ : Fin d₂ → CuspSub E a} {fam : Fin (d₁ + d₂) → CuspSub E a} {z₁ z₂ : ℂ}
    (he₁ : ∀ b, fam (Fin.castAdd d₂ b) = (fam₁ b).twist (Model.absC E z₁))
    (he₂ : ∀ b, fam (Fin.natAdd d₁ b) = (fam₂ b).twist (Model.absC E z₂)) {Φ : Sm E (r + s)}
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, Φ.1 (unip x * g) = Φ.1 g)
    (hsl : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (F₁ : Fin n → Sm E r) (F₂ : Fin n → Sm E s),
      (∀ i, F₁ i ∈ tw (indForms h₁ fam₁) z₁) ∧ (∀ i, F₂ i ∈ tw (indForms h₂ fam₂) z₂) ∧
      ∀ m : GA E r × GA E s, Φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (F₁ i).1 m.1 * (F₂ i).1 m.2)
    (hsm : Φ ∈ GlobalTheory.PRep.smoothPart (finRep E (r + s))) (hfv : Φ ∈ finVec (cptRep E (r + s))) :
    Φ ∈ indForms H fam := by
  have key : ∀ w ∈ unipRad (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H), ∀ (m : Fin (d₁ + d₂) → GA E a)
      (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
      Φ.1 (w * leviEmb (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m *
        (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
      Φ.1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m *
        (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) := by
    intro w hw m k g
    obtain ⟨x, w₁, w₂, hw₁, hw₂, rfl⟩ := unipRad_split h₁ h₂ H hw
    obtain ⟨n, F₁, F₂, hF₁, hF₂, hΦ⟩ := hsl k g
    rw [leviEmb_split h₁ h₂ H, mul_assoc (unip x), ← map_mul, Prod.mk_mul_mk, mul_assoc, hu, hΦ, hΦ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tw_unip_inv (hF₁ i) w₁ hw₁, tw_unip_inv (hF₂ i) w₂ hw₂]
  refine ⟨fun u hu g' => ?_, hsm, hfv, fun k g => ?_⟩
  · obtain ⟨u', hu', m, k, gf, rfl⟩ := GlobalTheory.IwasawaAdelic.iwasawa E (fun _ => a) H g'
    have e : ∀ X Y Z W : GA E (r + s), X * (Y * Z * W) = X * Y * Z * W := fun _ _ _ _ => by simp only [mul_assoc]
    rw [e, key _ (mul_mem hu hu'), key _ hu']
  · obtain ⟨n, F₁, F₂, hF₁, hF₂, hΦ⟩ := hsl k g
    have hmem : ∀ i, (fun m : Fin (d₁ + d₂) → GA E a =>
        (F₁ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₁ => a) h₁) (fun b => m (Fin.castAdd d₂ b))) *
        (F₂ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₂ => a) h₂) (fun b => m (Fin.natAdd d₁ b)))) ∈
          tensorForms (n := fun _ => a) fam := by
      intro i
      have e₁ : (fun b => fam (Fin.castAdd d₂ b)) = fun b => (fam₁ b).twist (Model.absC E z₁) := funext he₁
      have e₂ : (fun b => fam (Fin.natAdd d₁ b)) = fun b => (fam₂ b).twist (Model.absC E z₂) := funext he₂
      refine tensorForms_append fam
        (G₁ := fun m₁ => (F₁ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₁ => a) h₁) m₁))
        (G₂ := fun m₂ => (F₂ i).1 (leviEmb (Ad E) (stdBlocks (fun _ : Fin d₂ => a) h₂) m₂)) ?_ ?_
      · rw [e₁]; exact tw_slice_mem (hF₁ i)
      · rw [e₂]; exact tw_slice_mem (hF₂ i)
    convert Submodule.sum_mem _ (fun i _ => hmem i) using 1
    funext m
    rw [Finset.sum_apply, leviEmb_split h₁ h₂ H, hΦ]

end PositivityTheory.Rg.Rs.InductionInStages

end
end

