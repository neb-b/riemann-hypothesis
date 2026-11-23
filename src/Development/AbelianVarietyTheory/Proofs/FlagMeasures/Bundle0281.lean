module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometriesFixingBothFramesStabilizingLatti
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabFin

section Core

variable {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]

theorem finite_of_fix (hT : V →ₗ⋆[E] V →ₗ[E] E) (U : Submodule E V)
    (hpos : ∀ x ∈ (⨅ u ∈ U, LinearMap.ker (hT u)), x ≠ 0 → 0 < Algebra.trace ℚ E (hT x x))
    (Λ₀ : Submodule (𝓞 E) V) (hΛ : Submodule.IsFullLattice E Λ₀) :
    {h : V ≃ₗ[E] V | h ∈ Formalism.HermitianLatticesTheory.isom hT ∧ (∀ u ∈ U, h u = u) ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  set W : Submodule E V := ⨅ u ∈ U, LinearMap.ker (hT u) with hWdef
  have memW : ∀ y, y ∈ W ↔ ∀ x ∈ U, hT x y = 0 := fun y => by
    simp [hWdef, Submodule.mem_iInf]
  have hdisj : U ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, hxW⟩
    by_contra hx0
    have := hpos x hxW hx0
    rw [(memW x).1 hxW x hxU] at this
    simp at this
  have hsup : U ⊔ W = ⊤ := by
    let b := Module.finBasis E U
    let φ : V →ₗ[E] (Fin (Module.finrank E U) → E) := LinearMap.pi fun i => hT (b i : V)
    have hker : LinearMap.ker φ ≤ W := by
      intro y hy
      rw [memW]
      intro x hx
      have hy' : ∀ i, hT (b i : V) y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx', map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy' i, smul_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U := by
      refine (Submodule.finrank_le _).trans ?_
      simp
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hdisj, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    have h5 := Submodule.finrank_le (U ⊔ W)
    omega
  have hmul : ∀ v : V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ₀ := fun v => by
    have hv : v ∈ Submodule.span E (Λ₀ : Set V) := by rw [Submodule.IsFullLattice.span_eq_top (self := hΛ)]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩
  let L : Submodule (𝓞 E) W := Λ₀.comap (W.subtype.restrictScalars (𝓞 E))
  have hfg : L.FG := by
    apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars (𝓞 E)) Subtype.val_injective
    exact hΛ.fg.of_le (Submodule.map_comap_le _ _)
  haveI : Submodule.IsLattice E L := Submodule.IsLattice.of_fg E hfg
  let hW := hT.domRestrict₁₂ W W
  have hposW : ∀ w : W, w ≠ 0 → 0 < Algebra.trace ℚ E (hW w w) := fun w hw =>
    hpos w w.2 fun h0 => hw (Subtype.ext h0)
  obtain ⟨N, hN⟩ := hfg
  have hNL : ∀ n ∈ N, ((n : W) : V) ∈ Λ₀ := fun n hn => by
    have : n ∈ L := hN ▸ Submodule.subset_span hn
    exact this
  have hpres : ∀ h : V ≃ₗ[E] V, h ∈ Formalism.HermitianLatticesTheory.isom hT → (∀ u ∈ U, h u = u) → ∀ w ∈ W, h w ∈ W := by
    intro h hiso hfix w hw
    rw [memW] at hw ⊢
    intro x hx
    rw [← hfix x hx, hiso x w]
    exact hw x hx
  refine Set.Finite.of_finite_image (f := fun (h : V ≃ₗ[E] V) (n : N) => h ((n : W) : V)) ?_ ?_
  · refine (Set.Finite.pi (t := fun n : N => Subtype.val '' {v : W | v ∈ L ∧
        Algebra.trace ℚ E (hW v v) ≤ Algebra.trace ℚ E (hW (n : W) (n : W))})
      fun n => (Formalism.HermitianLatticesTheory.autFinite_short hW hposW L _).image _).subset ?_
    rintro _ ⟨h, ⟨hiso, hfix, hlat⟩, rfl⟩ n _
    refine ⟨⟨h ((n : W) : V), hpres h hiso hfix _ (n : W).2⟩, ⟨?_, ?_⟩, rfl⟩
    · have hm : ((h : V →ₗ[E] V).restrictScalars (𝓞 E)) ((n : W) : V) ∈ Formalism.HermitianLatticesTheory.gmap h Λ₀ :=
        Submodule.mem_map_of_mem (hNL n n.2)
      rw [hlat] at hm
      exact hm
    · show Algebra.trace ℚ E (hT (h ((n : W) : V)) (h ((n : W) : V))) ≤
        Algebra.trace ℚ E (hT ((n : W) : V) ((n : W) : V))
      rw [hiso]
  · rintro h₁ ⟨-, hf1, -⟩ h₂ ⟨-, hf2, -⟩ heq
    let K : Submodule E V := LinearMap.ker ((h₁ : V →ₗ[E] V) - (h₂ : V →ₗ[E] V))
    have memK : ∀ x, x ∈ K ↔ h₁ x = h₂ x := fun x => by
      simp [K, LinearMap.mem_ker, sub_eq_zero]
    have hLK : L ≤ (K.restrictScalars (𝓞 E)).comap (W.subtype.restrictScalars (𝓞 E)) := by
      rw [← hN]
      refine Submodule.span_le.2 fun n hn => ?_
      show ((n : W) : V) ∈ K
      rw [memK]
      exact congrFun heq ⟨n, hn⟩
    have hWK : W ≤ K := by
      intro w hw
      obtain ⟨d, hd0, hd⟩ := hmul w
      have h1 : (⟨d • w, W.smul_of_tower_mem d hw⟩ : W) ∈ L := hd
      have h2 : d • w ∈ K := hLK h1
      rw [← algebraMap_smul E d w] at h2
      exact (Submodule.smul_mem_iff K
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h2
    have hUK : U ≤ K := fun u hu => by rw [memK, hf1 u hu, hf2 u hu]
    have htop : ⊤ ≤ K := hsup ▸ sup_le hUK hWK
    exact LinearEquiv.ext fun x => (memK x).1 (htop trivial)

end Core

theorem stab_finite : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  intro D T T' F F' hpos Λ₀ hΛ
  refine (finite_of_fix (VS D).hT (Xplus F ⊔ Xplus F') hpos Λ₀ hΛ).subset ?_
  rintro h ⟨⟨hiso, hF, hF'⟩, hlat⟩
  refine ⟨hiso, ?_, hlat⟩
  have key : ∀ {T0 : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T0), (∀ a, h (frame G a) = frame G a) →
      Xplus G ≤ LinearMap.ker ((h : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id) := by
    intro T0 G hG
    have he : ∀ i, h (G.fl.e i) = G.fl.e i := fun i => by
      have := hG (Fin.castSucc i)
      simpa [frame, FlagG.fvec] using this
    have hz : h G.fl.z = G.fl.z := by
      have := hG (Fin.last _)
      simpa [frame, FlagG.fvec] using this
    show Submodule.span D.host.E (Set.range G.fl.e) ⊔ Submodule.span D.host.E {G.fl.z} ≤ _
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      simp [he i]
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simp [hz]
  intro u hu
  have := (sup_le (key F hF) (key F' hF')) hu
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.StabFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedConvOfIntegralFlagLattice
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

noncomputable section

namespace GlobalTheory.FixConvRow

theorem loc_gen {E : Type} [Field E] [NumberField E] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ 0 ∧ ∃ s, s ∉ P.asIdeal ∧ ∀ y ∈ J, ∃ o : 𝓞 E, s * y = o * d := by
  first
  | exact @_root_.GlobalTheory.LocalGenerators.main
  | exact _root_.GlobalTheory.LocalGenerators.main
  | (apply _root_.GlobalTheory.LocalGenerators.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalGenerators.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalGenerators.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalGenerators.main ..)

end GlobalTheory.FixConvRow

namespace GlobalTheory.FixConvRow

open IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem locS_le_of_le {V : Type} [AddCommGroup V] [Module (𝓞 E) V] (M : Submonoid (𝓞 E)) {A B : Submodule (𝓞 E) V}
    (h : A ≤ Formalism.HermitianLatticesTheory.locS M B) : Formalism.HermitianLatticesTheory.locS M A ≤ Formalism.HermitianLatticesTheory.locS M B := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, htx⟩ := h hx
  exact ⟨t * s, M.mul_mem ht hs, by rw [mul_smul]; exact htx⟩

theorem locS_span_eq {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (M : Submonoid (𝓞 E)) {r : ℕ} (e : Fin r → V) (I : Fin r → Set E) (c : Fin r → E)
    (h1 : ∀ a, ∃ s ∈ M, algebraMap (𝓞 E) E s * c a ∈ I a)
    (h2 : ∀ a, ∀ x ∈ I a, ∃ s ∈ M, ∃ o : 𝓞 E, algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * c a) :
    Formalism.HermitianLatticesTheory.locS M (Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ I a ∧ y = x • e a}) =
      Formalism.HermitianLatticesTheory.locS M (Submodule.span (𝓞 E) (Set.range fun a => c a • e a)) := by
  have key : ∀ (s : 𝓞 E) (x : E) (v : V), s • (x • v) = (algebraMap (𝓞 E) E s * x) • v := by
    intro s x v
    rw [← smul_assoc, Algebra.smul_def]
  apply le_antisymm
  · apply locS_le_of_le
    rw [Submodule.span_le]
    rintro _ ⟨a, x, hx, rfl⟩
    obtain ⟨s, hs, o, ho⟩ := h2 a x hx
    refine ⟨s, hs, ?_⟩
    rw [key, ho, ← key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · apply locS_le_of_le
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs, hsc⟩ := h1 a
    refine ⟨s, hs, ?_⟩
    rw [key]
    exact Submodule.subset_span ⟨a, _, hsc, rfl⟩

theorem inv_gen (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    ∃ c : E, c ≠ 0 ∧ (∃ s ∈ P.asIdeal.primeCompl,
      algebraMap (𝓞 E) E s * c ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹)) ∧
      ∀ x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹), ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 E,
        algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * c := by
  obtain ⟨d, hdJ, hd0, s, hsP, hs⟩ := loc_gen P J hJ
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hJ
  have hd0' : algebraMap (𝓞 E) E d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)]
  refine ⟨(algebraMap (𝓞 E) E d)⁻¹, inv_ne_zero hd0', ⟨s, hsP, ?_⟩, fun x hx => ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    obtain ⟨o, ho⟩ := hs y' hy'
    rw [FractionalIdeal.mem_one_iff _]
    refine ⟨o, ?_⟩
    have e : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E y' = algebraMap (𝓞 E) E o * algebraMap (𝓞 E) E d := by
      rw [← map_mul, ← map_mul, ho]
    field_simp
    exact e.symm
  · rw [FractionalIdeal.mem_inv_iff hJ0] at hx
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hdJ, rfl⟩))
    refine ⟨o, ?_⟩
    rw [ho, map_one, one_mul]
    field_simp

theorem inv_one (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (t : 𝓞 E) (htJ : t ∈ J)
    (htP : t ∉ P.asIdeal) :
    (∃ s ∈ P.asIdeal.primeCompl,
      algebraMap (𝓞 E) E s * 1 ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹)) ∧
      ∀ x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹), ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 E,
        algebraMap (𝓞 E) E s * x = algebraMap (𝓞 E) E o * 1 := by
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hJ
  refine ⟨⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩, fun x hx => ⟨t, htP, ?_⟩⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0]
    intro y hy
    obtain ⟨y', -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [FractionalIdeal.mem_one_iff _]
    exact ⟨y', by simp⟩
  · rw [FractionalIdeal.mem_inv_iff hJ0] at hx
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨t, htJ, rfl⟩))
    exact ⟨o, by rw [ho, mul_one, mul_comm]⟩

end Gen

end GlobalTheory.FixConvRow

namespace GlobalTheory.FixConvRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ddS_zpow_eq (D : D7) (a : Fin D.R.rS) :
    (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) =
      ((↑((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^
        (D.R.rS - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  rw [FractionalIdeal.coeIdeal_pow, ← Nat.cast_sub a.2.le, zpow_neg, zpow_natCast]
  rfl

theorem absNorm_different_not_mem (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro hNP
  rw [gS, Nat.cast_mul] at hg
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rcases P.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hc := Nat.isCoprime_iff_coprime.2 (GlobalTheory.FrameIntegral.coprime_gi (D := D) i)
  obtain ⟨u, v, huv⟩ := hc.map (Int.castRingHom (𝓞 D.host.E))
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hNP) (P.asIdeal.mul_mem_left _ hi)

theorem isFixedConv_of_XLam_eq : ∀ (D : D7) (T : D.host.E) (F : FlagG (VS D) D.R.rS T) (Λ : LV D),
    XLam Λ (lf D F) = XS D F → (∀ c : D.host.E, c • F.z ∈ Lsub Λ (lf D F) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) →
    IsFixedConv Λ (gS D) (lf D F) := by
  intro D T F Λ hX hprim
  refine ⟨fun P => ?_, hprim⟩
  have hJd0 : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 D.host.F))
  have hJm : ∀ m : ℕ, Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ^ m ≠ ⊥ :=
    fun m => pow_ne_zero m hJd0
  have goal : ∀ c : Fin D.R.rS → D.host.E,
      (∀ a : Fin D.R.rS, ∃ s ∈ P.asIdeal.primeCompl, algebraMap (𝓞 D.host.E) D.host.E s * c a ∈
        (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) →
      (∀ a : Fin D.R.rS, ∀ x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
        ∃ s ∈ P.asIdeal.primeCompl, ∃ o : 𝓞 D.host.E,
          algebraMap (𝓞 D.host.E) D.host.E s * x = algebraMap (𝓞 D.host.E) D.host.E o * c a) →
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F)) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • (lf D F).fl.e a))) := by
    intro c h1 h2
    rw [hX]
    exact locS_span_eq _ F.e
      (fun a => ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Set D.host.E)) c h1 h2
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · have hN : ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) : ℕ) : 𝓞 D.host.E) ∈
        Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) := by
      have h := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
        (Ideal.absNorm_mem (differentIdeal ℤ (𝓞 D.host.F)))
      simpa using h
    have hNP := absNorm_different_not_mem D P hg
    have hone := fun a : Fin D.R.rS => inv_one P _ (hJm (D.R.rS - (a : ℕ))) _ (Ideal.pow_mem_pow hN _)
      (fun h => hNP (P.isPrime.mem_of_pow_mem _ h))
    refine ⟨fun _ => 1, fun _ => one_ne_zero, fun _ _ => rfl, goal _ ?_ ?_⟩
    · intro a; rw [ddS_zpow_eq]; exact (hone a).1
    · intro a; rw [ddS_zpow_eq]; exact (hone a).2
  · choose c hc0 hc1 hc2 using fun a : Fin D.R.rS => inv_gen P _ (hJm (D.R.rS - (a : ℕ)))
    refine ⟨c, hc0, fun h => absurd h hg, goal c ?_ ?_⟩
    · intro a; rw [ddS_zpow_eq]; exact hc1 a
    · intro a; rw [ddS_zpow_eq]; exact hc2 a

end GlobalTheory.FixConvRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFlagFrameVectorMemRowLattice
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.RowFrame

theorem one_mem_ddS_zpow (D : D7) (n : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hI0 : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    rw [Ideal.map_eq_bot_iff_of_injective]
    · exact differentIdeal_ne_bot
    · exact FaithfulSMul.algebraMap_injective _ _
  have hI1 : ddS D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hJ0 : ddS D ^ n ≠ 0 := pow_ne_zero _ hI0
  have hJ1 : ddS D ^ n ≤ 1 := pow_le_one' hI1 n
  rw [zpow_neg, zpow_natCast]
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ (ddS D ^ n)⁻¹ := by
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = ddS D ^ n * (ddS D ^ n)⁻¹ :=
          (mul_inv_cancel₀ hJ0).symm
      _ ≤ 1 * (ddS D ^ n)⁻¹ := by gcongr
      _ = (ddS D ^ n)⁻¹ := one_mul _
  exact h1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)

theorem frame_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D) :
    IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  rintro ⟨-, ⟨-, -, hlift, -⟩, hX⟩ a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z := by simp [frame, FlagG.fvec]
    rw [e]
    exact hlift.1
  · have e : frame (lf D F0) i.castSucc = F0.e i := by simp [frame, FlagG.fvec]
    rw [e]
    have hmem : F0.e i ∈ XS D F0 := by
      apply Submodule.subset_span
      refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
      have hk : (-((D.R.rS : ℤ) - ((i : ℕ) : ℤ))) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
        rw [Nat.cast_sub i.isLt.le]
      rw [hk]
      exact one_mem_ddS_zpow D _
    rw [← hX] at hmem
    exact hmem.1

end GlobalTheory.Unfold.RowFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryMapFlagSpaces
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem adapt_map_flag (D : D7) (T : D.host.E) (F G : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D) (hg : Adapt g F G) :
    (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧
      (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  have hmono : ∀ (H : LFlag (D.sp.Y 0) D.R.rS T) {a b : ℕ}, a ≤ b → Xflag H a ≤ Xflag H b := by
    intro H a b hab
    exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi hab : i.1 < b))
  have hmem : ∀ (H : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) {j : ℕ}, i.1 < j → H.fl.e i ∈ Xflag H j := by
    intro H i j hij
    exact Submodule.subset_span ⟨i, hij, rfl⟩
  have hX : ∀ H : LFlag (D.sp.Y 0) D.R.rS T, Xsp H = Xflag H D.R.rS := by
    intro H
    show Submodule.span _ (Set.range H.fl.e) = Submodule.span _ (H.fl.e '' {i | i.1 < D.R.rS})
    congr 1
    ext x
    simp
  have hstep : ∀ i : Fin D.R.rS, g (F.fl.e i) - G.fl.e i ∈ Xflag G i.1 := by
    intro i
    have := hg.2 i.castSucc
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have hle : ∀ j, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
    intro j
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    show g (F.fl.e i) ∈ Xflag G j
    have h1 := hmono G (le_of_lt hi) (hstep i)
    have h2 := hmem G i hi
    simpa using add_mem h1 h2
  have hge : ∀ j, Xflag G j ≤ (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    intro j
    induction j with
    | zero =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hmap : (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.map_mono (hmono F (Nat.le_succ j))
      have h1 : g (F.fl.e i) - G.fl.e i ∈ (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        hmap (ih (hmono G hi' (hstep i)))
      have h2 : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) ∈
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.mem_map_of_mem (hmem F i hi)
      have h3 := sub_mem h2 h1
      simp only [LinearEquiv.coe_coe, sub_sub_cancel] at h3
      exact h3
  refine ⟨fun j => le_antisymm (hle j) (hge j), ?_⟩
  rw [hX F, hX G]
  exact le_antisymm (hle _) (hge _)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_isometry_extends_local_isometry : ∀ (D : D7) (Z : LocDat D), ∀ (p : PlF D), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃ g, Ext p γ g ∧ LocNG.IsUnitary (locH Z p) g ∧ (∀ g', Ext p γ g' → g' = g) ∧ (∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap γ Λ)) ∧ ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), γ ∈ Formalism.L2.SG.NGData.NRat F → g ∈ NU (locH Z p) (scaled Z p (frame F)) := by
  first | exact @GlobalTheory.LocExt.ext_isometry | exact GlobalTheory.LocExt.ext_isometry | (intros; apply GlobalTheory.LocExt.ext_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.RatDiscrete

theorem subgroup_countable_discrete : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite :=
  fun I => ⟨⟨ratSub I, rfl⟩, countable_GFset I,
    fun _ hC => Set.inter_comm _ _ ▸ finite_inter I hC⟩

end GlobalTheory.RatDiscrete
end

