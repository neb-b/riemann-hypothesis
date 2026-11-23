module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthShift

open GlobalTheory.StdFrames (cpt mem_OA_iff comp_toAd toAd toAd_spec)
open scoped Pointwise

variable {D : D7}

theorem modul_mem_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {r : 𝓞 D.host.E}
    (hr : r ∈ G.modul) : (r : D.host.E) ∈ shiftId G := by
  have h0 : G.pl.modulBar sc ≠ ⊥ := by
    intro h
    apply G.pl.modul_ne_bot sc
    unfold Places.modulBar at h
    have := congrArg (fun J => D.host.conj⁻¹ • J) h
    simpa using this
  have h1 := FractionalIdeal.one_mem_inv_coe_ideal (K := D.host.E) h0
  have h2 : (r : D.host.E) ∈ ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hr
  simpa [shiftId] using FractionalIdeal.mul_mem_mul h2 h1

theorem smul_mem_idLat {n : ℕ} {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {r : 𝓞 D.host.E} (hr : (r : D.host.E) ∈ J)
    {t : Fin n → D.host.E} (ht : t ∈ idLat I Λ) : r • t ∈ idLat (I * J) Λ := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨s * r, FractionalIdeal.mul_mem_mul hs hr, y, hy, ?_⟩
    rw [mul_comm, mul_smul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

variable {S B : HSp D} {LS : Lat S} {LT LT' : Lat B}

theorem inc_smul_mem {r : 𝓞 D.host.E} (hr : ∀ t ∈ LT, r • t ∈ LT') {u : WO S B}
    (hu : u ∈ latO S B (LS : Set _) (LT : Set _) fun _ => True) :
    incA D (r : D.host.E) • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, r • t, hr t ht, ?_⟩
    ext i j
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * ((r : D.host.E) * t i) * _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mul_eq_of_toEAf {b b' x : AE D} (h : toEAf D b = toEAf D b') (h0 : infPart D x = 0) : b * x = b' * x := by
  have h1 : infPart D ((b - b') * x) = 0 := ((infPart D).map_mul _ _).trans (by rw [h0, mul_zero])
  have h2 : toEAf D (b - b') = 0 := ((toEAf D).map_sub _ _).trans (sub_eq_zero.2 h)
  have h3 : toEAf D ((b - b') * x) = 0 := ((toEAf D).map_mul _ _).trans (by rw [h2, zero_mul])
  have h4 := (comp_toAd D).ext _ h1 ((congrArg (toAd D) h3).trans (toAd D).map_zero)
  exact sub_eq_zero.1 ((sub_mul b b' x).symm.trans h4)

theorem exists_lift_int (c : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ c' : AE D, toEAf D c' = c.1 ∧ finPart D c' ∈ intAE D := by
  obtain ⟨c', -, hc'⟩ := (comp_toAd D).surj (toAd D c.1)
  refine ⟨c', GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D) hc', ((comp_toAd D).int c').2 fun Q => ?_⟩
  rw [hc']
  exact (mem_OA_iff _).1 c.2 Q


set_option maxHeartbeats 800000 in
theorem smul_mem_of_idS {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : ∀ r ∈ 𝔪, ∀ t ∈ LT, r • t ∈ LT') {u : WO S B}
    (hu : u ∈ latO S B (LS : Set _) (LT : Set _) fun _ => True) {s : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hs : s ∈ Formalism.L2.DIV.idS D.host.F 𝔪) {b : AE D} (hb : toEAf D b = s.1) :
    b • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
  have key : ∃ b' : AE D, toEAf D b' = s.1 ∧ b' • u ∈ latO S B (LS : Set _) (LT' : Set _) fun _ => True := by
    clear hb
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      exact ⟨incA D (r : D.host.E), rfl, inc_smul_mem (h𝔪 r hr) hu⟩
    | zero => exact ⟨0, RingHom.map_zero _, by rw [zero_smul]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨c, hc, hc'⟩ := hy
      exact ⟨a + c, by rw [RingHom.map_add (f := _), ha, hc, Subring.coe_add], by rw [add_smul]; exact add_mem ha' hc'⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨c', hc, hc'⟩ := exists_lift_int c
      refine ⟨c' * a, ((toEAf D).map_mul c' a).trans (congrArg₂ (· * ·) hc ha), ?_⟩
      rw [mul_smul]
      exact GlobalTheory.LatticeStable.smul_mem_latO D S B _ _ _ _ hc' _ ha'
  obtain ⟨b', hb', hm⟩ := key
  have e : b • u = b' • u := Matrix.ext fun i j =>
    mul_eq_of_toEAf (hb.trans hb'.symm) (GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 (GlobalTheory.FinPl.LatMem.latO_mxAt hu i j)).1
  rw [e]
  exact hm

theorem mem_latO_shift : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) {S B : HSp D} (LS : Lat S) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ₀ : Lat B), IsSelfDualC S LS → IsSelfDualC B (idLat I Λ₀) → IsSelfDualC B (idLat (I * shiftId G) Λ₀) → ∀ z : WO S B, z ∈ latO S B (LS : Set _) (idLat I Λ₀ : Set _) (fun _ => True) → (∃ e, IsIdemSum e G.pl.W0 ∧ e • z ∈ hatMx (G.modul • homLat LS (idLat I Λ₀))) → z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) (fun _ => True) := by
  intro D hOff T L μ0 hL sc G S B LS I Λ₀ hS _ _ z hz ⟨e, he, hez⟩
  have h𝔪 : ∀ r ∈ G.modul, ∀ t ∈ idLat I Λ₀, r • t ∈ idLat (I * shiftId G) Λ₀ :=
    fun r hr t ht => smul_mem_idLat (modul_mem_shiftId G hr) ht
  have hle : G.modul • homLat LS (idLat I Λ₀) ≤ homLat LS (idLat (I * shiftId G) Λ₀) :=
    Submodule.smul_le.2 fun r hr x hx y hy => by
      rw [smul_mulVec]
      exact h𝔪 r hr _ (hx y hy)
  have h1 : e • z ∈ latO S B (LS : Set _) (idLat (I * shiftId G) Λ₀ : Set _) fun _ => True := by
    refine GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hS he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hOff hL G) (fun i j => ?_) ?_
    · change e * (e * z i j) = e * z i j
      rw [← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
    · refine AddSubgroup.closure_mono ?_ hez
      rintro _ ⟨α, hα, x, hx, rfl⟩
      exact ⟨α, hα, x, hle hx, rfl⟩
  obtain ⟨-, e1, e2⟩ := Comparison₂.cpt_idemSum he
  have hint : toEAf D (1 - e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (mem_OA_iff _).2 fun Q => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
    by_cases hQ : Q ∈ G.pl.W0
    · rw [e1 Q hQ, sub_self]; exact zero_mem _
    · rw [e2 Q hQ, sub_zero]; exact one_mem _
  have hid : (⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F G.modul := by
    refine (Comparison₂.mem_idS_modul G _).2 fun w hw => ?_
    change Valued.v (cpt (D := D) w (toEAf D (1 - e))) ≤ _
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
    exact zero_le
  have h2 := smul_mem_of_idS (LS := LS) h𝔪 hz hid rfl
  have h3 := add_mem h1 h2
  rwa [← add_smul, add_sub_cancel, one_smul] at h3

end GlobalTheory.DepthShift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateHalfCommutantActsOnCosetVectorByScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosScalar

variable {D : D7}

theorem selfDual_full (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this


theorem smul_mem_hatMx_of_fr {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (Lev.EAf D)} {β' : GL (Fin m) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {z : Mx D m n}
    (hz : ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F 𝔪, s.1 = GlobalTheory.FunObj.Comparison₂.fr β' β (z.map (toEAf D)) i j) :
    a • z ∈ hatMx (𝔪 • homLat Λ Λ') := by
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪]
  refine ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul, map_mul, ha0, zero_mul], fun i j => ?_⟩
  obtain ⟨s, hs, hse⟩ := hz i j
  refine ⟨⟨toEAf D a, ha⟩ * s, Ideal.mul_mem_left _ _ hs, ?_⟩
  have e2 : GlobalTheory.FunObj.Comparison₂.fr β' β ((a • z).map (toEAf D)) i j = toEAf D a * GlobalTheory.FunObj.Comparison₂.fr β' β (z.map (toEAf D)) i j := by
    simp only [GlobalTheory.FunObj.Comparison₂.fr, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  exact (congrArg (toEAf D a * ·) hse).trans e2.symm

theorem exists_frames {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hΛ' : Submodule.IsFullLattice D.host.E Λ') :
    ∃ β : GL (Fin n) (Lev.EAf D), ∃ β' : GL (Fin m) (Lev.EAf D), Formalism.L2.DIV.IsFrame β Λ ∧ Formalism.L2.DIV.IsFrame β' Λ' := by
  obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ hΛ.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ))
  obtain ⟨β', hβ'⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ' hΛ'.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ'))
  exact ⟨β, β', hβ, hβ'⟩

theorem smul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hΛ' : Submodule.IsFullLattice D.host.E Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {z : Mx D m n}
    (hz : z ∈ hatMx (𝔪 • homLat Λ Λ')) : a • z ∈ hatMx (𝔪 • homLat Λ Λ') := by
  obtain ⟨β, β', hβ, hβ'⟩ := exists_frames hΛ hΛ'
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪] at hz
  exact smul_mem_hatMx_of_fr hβ hβ' 𝔪 ha0 ha hz.2

theorem smul_map_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hΛ' : Submodule.IsFullLattice D.host.E Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {y : Matrix (Fin m) (Fin n) D.host.E} (hy : y ∈ 𝔪 • homLat Λ Λ') :
    a • y.map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  obtain ⟨β, β', hβ, hβ'⟩ := exists_frames hΛ hΛ'
  exact smul_mem_hatMx_of_fr hβ hβ' 𝔪 ha0 ha (GlobalTheory.FunObj.Comparison₂.fr_mem_idS hβ hβ' hy)

theorem hatMx_smul_le {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (𝔪 : Ideal (𝓞 D.host.E)) :
    hatMx (𝔪 • homLat Λ Λ') ≤ hatMx (homLat Λ Λ') :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, x, hx, e⟩ => ⟨α, hα, x, Submodule.smul_le_right hx, e⟩

theorem sub_mem_of_cosSet {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hΛ' : Submodule.IsFullLattice D.host.E Λ') {𝔪 : Ideal (𝓞 D.host.E)} {e : AE D}
    (he0 : infPart D e = 0) (he : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {κ : Cos Λ Λ' 𝔪}
    {t t' : Mx D m n} (ht : t ∈ cosSet e κ) (ht' : t' ∈ cosSet e κ) : t - t' ∈ hatMx (𝔪 • homLat Λ Λ') := by
  obtain ⟨-, x₀, hx₀, hd⟩ := ht
  obtain ⟨-, x₁, hx₁, hd'⟩ := ht'
  have hy : x₀.1 - x₁.1 ∈ 𝔪 • homLat Λ Λ' := GlobalTheory.FunObj.Comparison₂.sub_mem_of_mk_eq (hx₀.trans hx₁.symm)
  have e1 : t - t' = (t - e • (↑x₀ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) -
      (t' - e • (↑x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) + e • (x₀.1 - x₁.1).map (incA D) := by
    rw [Matrix.map_sub _ (map_sub (incA D)), smul_sub]; abel
  rw [e1]
  exact add_mem (sub_mem hd hd') (smul_map_mem_hatMx hΛ hΛ' 𝔪 he0 he hy)

end GlobalTheory.CosScalar


set_option maxHeartbeats 2000000 in
open GlobalTheory.CosScalar in
theorem GlobalTheory.CosScalar.conjHalf_heisO_cosVec_smul : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → (∀ κ, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd e κ) (W.cosVec i κ)) → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∀ κ, ∃ c : ℂ, heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (cA D e • w) (W.cosVec i κ) = c • W.cosVec i κ := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he hT w hw hinf κ
  have hsd := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hprops := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0 (fun _ => 0) he
  have he0 : infPart D e = 0 := hprops.1
  have heint := hprops.2.1
  obtain ⟨⟨es, hes, hesum⟩, -⟩ := id he
  have hee : e * e = e := by
    conv_lhs => rw [hesum, Finset.sum_mul]
    rw [hesum]
    exact Finset.sum_congr rfl fun P hP => GlobalTheory.IdemSumLoc.idem_mul_sum hes (hesum ▸ he.2) hP

  have hkey : ∀ u : WO (G.pS (.chi i 0)) (G.pT (.chi i 0)), IsHalf e u →
      u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) →
      W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w u) = 1 := by
    intro u hu hm
    have hlat : u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _)
        fun _ => True :=
      GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd.1 he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hQ hL G) hu (hatMx_smul_le _ _ _ hm)
    have hsplit : u = ∑ P ∈ G.pl.W0, es P • u := by
      rw [← Finset.sum_smul, ← hesum]
      ext a b
      rw [Matrix.smul_apply, smul_eq_mul, hu a b]
    have hsum : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (∑ P ∈ G.pl.W0, es P • u) =
        ∑ P ∈ G.pl.W0, symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w (es P • u) :=
      map_sum (AddMonoidHom.mk' (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) w)
        (GlobalTheory.Core.Rk.ThetaOf.symplO_add_right _ _ w)) _ _
    rw [hsplit, hsum]
    refine Finset.sum_induction _ (fun x => W.ψ x = 1) (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, one_mul])
      (AddChar.map_zero_eq_one _) fun P hP => ?_
    have hsp : IsSplitIdem D (es P) := (hes P hP).1
    have hPsum : IsIdemSum (es P) {P} :=
      ⟨⟨es, fun Q hQ => by rw [Finset.mem_singleton.1 hQ]; exact hes P hP, by rw [Finset.sum_singleton]⟩, hsp.2.1⟩
    have hPp := GlobalTheory.IdemSumIdeal.isIdemSum_props (es P) {P} (fun _ => 0) hPsum
    refine hw.2 (es P) hsp (es P • u) ⟨GlobalTheory.CosetRow.smul_mem_latO_idem _ _ hsp.1 hlat, fun e' he' => ?_⟩ fun a b => ?_
    · rw [smul_smul]
      have hp' := GlobalTheory.IdemSumIdeal.isIdemSum_props e' G.pl.W0 (fun _ => 0) he'
      exact smul_mem_hatMx (selfDual_full _ _ hsd.1) (selfDual_full _ _ hsd.2) _ (by rw [map_mul, hp'.1, zero_mul])
        (by rw [map_mul]; exact mul_mem hp'.2.1 hPp.2.1) hm
    · show es P * (es P * u a b) = es P * u a b
      rw [← mul_assoc, hsp.1]
  have hyH : IsHalf (cA D e) (cA D e • w) := fun a b => by
    show cA D e * (cA D e * w a b) = cA D e * w a b
    rw [← mul_assoc, ← map_mul, hee]
  have hconst : ∀ t ∈ cosSet e κ, ∀ t' ∈ cosSet e κ,
      W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t (cA D e • w)) =
        W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t' (cA D e • w)) := by
    intro t ht t' ht'
    have hu : IsHalf e (t - t') := fun a b => by
      show e * (t a b - t' a b) = t a b - t' a b
      rw [mul_sub, ht.1 a b, ht'.1 a b]
    have hm := sub_mem_of_cosSet (selfDual_full _ _ hsd.1) (selfDual_full _ _ hsd.2) he0 heint ht ht'
    have h1 : W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (t - t') (cA D e • w)) = 1 := by
      rw [GlobalTheory.BigDat.symplO_cA_smul, show e • (t - t') = t - t' from Matrix.ext fun a b => hu a b,
        GlobalTheory.Asc.psi_symplO_swap]
      exact hkey _ hu hm
    have e1 : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t (cA D e • w) =
        symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (t - t') (cA D e • w) +
          symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t' (cA D e • w) := by
      rw [← GlobalTheory.Core.Rk.ThetaOf.symplO_add_left, sub_add_cancel]
    rw [e1, AddChar.map_add_eq_mul, h1, one_mul]
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hT κ
  have hcv : W.cosVec i κ = Tm (cosInd e κ) := hall Tm hTm
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd hsd.1 hsd.2 (G.pl.modul_ne_bot sc) hee he0 κ
  have hmod := hTm.modul (cosInd e κ) hSB (cA D e • w) hyH
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (fun t => W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t (cA D e • w)) * cosInd e κ t) =
      c • cosInd e κ := by
    by_cases hne : (cosSet e κ).Nonempty
    · obtain ⟨t₀, ht₀⟩ := hne
      refine ⟨W.ψ (symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) t₀ (cA D e • w)), funext fun t => ?_⟩
      by_cases ht : t ∈ cosSet e κ
      · have h1 : cosInd e κ t = 1 := by simp [cosInd, ht]
        rw [Pi.smul_apply, h1, hconst t ht t₀ ht₀, smul_eq_mul]
      · have h0 : cosInd e κ t = 0 := by simp [cosInd, ht]
        rw [Pi.smul_apply, h0, mul_zero, smul_zero]
    · refine ⟨0, funext fun t => ?_⟩
      have ht : t ∉ cosSet e κ := fun h => hne ⟨t, h⟩
      have h0 : cosInd e κ t = 0 := by simp [cosInd, ht]
      rw [Pi.smul_apply, h0, mul_zero, smul_zero]
  exact ⟨c, by rw [hcv, ← hmod, hc, map_smul]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowSmulMemSelfDualModulusShift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
namespace GlobalTheory.DepHalf

open scoped Pointwise

theorem smul_mem_latBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D →
    ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i := by
  intro D T L sc μ₀ hL hQ G i hi e he u hu
  have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hone : (1 : D.host.E) ∈ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
    have hle : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
      have := FractionalIdeal.inv_anti_mono hmB FractionalIdeal.coeIdeal_le_one
      rwa [inv_one] at this
    exact hle (FractionalIdeal.one_mem_one _)
  have hsub : G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)) ≤
      homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    refine Submodule.smul_le.2 fun r hr x hx y hy => ?_
    rw [smul_mulVec]
    refine Submodule.subset_span ⟨algebraMap (𝓞 D.host.E) D.host.E r, ?_, x *ᵥ y, hx y hy, ?_⟩
    · unfold shiftId
      rw [show algebraMap (𝓞 D.host.E) D.host.E r = algebraMap (𝓞 D.host.E) D.host.E r * 1 by rw [mul_one]]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hr) hone
    · exact (algebraMap_smul D.host.E r (x *ᵥ y)).symm
  have h2 : e • u ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) := by
    refine AddSubgroup.closure_mono ?_ h1
    rintro w ⟨α, hα, x, hx, rfl⟩
    exact ⟨α, hα, x, hsub hx, rfl⟩
  have hhalf : IsHalf e (e • u) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) := (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  exact GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hQ hL G) hhalf h2

end GlobalTheory.DepHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedUnipotentRadicalAtRealPlaceTrivialAtPlac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem isClosed_cmp_eq_one {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) :
    IsClosed {p : NI V C | cmp θ τ (p : GA D V) = 1} :=
  isClosed_eq ((GlobalTheory.Cusp.KinfCompact.continuous_realMat hθ V τ).comp continuous_subtype_val)
    continuous_const

theorem isClosed_atP_and_isClosed_offP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau), IsClosed (GlobalTheory.FibreAtTau.atP θ V C τ : Set (NI V C)) ∧ IsClosed (GlobalTheory.FibreAtTau.offP θ V C τ : Set (NI V C)) := by
  intro D θ hθ V r C τ
  constructor
  · have e : (atP θ V C τ : Set (NI V C)) = (Subtype.val ⁻¹' (GinfC V : Set (GA D V))) ∩
        ⋂ (τ' : D.what₂.Tau) (_ : τ' ≠ τ), {p : NI V C | cmp θ τ' (p : GA D V) = 1} := by
      ext p
      simp only [SetLike.mem_coe, mem_atP, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [e]
    exact ((GlobalTheory.Cusp.KinfCompact.isClosed_realPts V).preimage continuous_subtype_val).inter
      (isClosed_iInter fun τ' => isClosed_iInter fun _ => isClosed_cmp_eq_one hθ V C τ')
  · have e : (offP θ V C τ : Set (NI V C)) = {p : NI V C | cmp θ τ (p : GA D V) = 1} := by
      ext p
      simp only [SetLike.mem_coe, mem_offP, Set.mem_ofPred_eq]
    rw [e]
    exact isClosed_cmp_eq_one hθ V C τ

end GlobalTheory.FibreAtTau
end

