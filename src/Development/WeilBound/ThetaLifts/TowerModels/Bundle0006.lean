module

public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0003
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0003
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle0002
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsFinitePlaceVacuumAnyDarbouxCoordinates
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
public import Development.WeilBound.ThetaLifts.TowerModels.StabCpt

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.ModelEx
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem modelEx : ModelEx := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := Tw.RatDarboux.exists_rational_darboux_of_isGood B hB X W r s r' s' hX hW
  obtain ⟨-, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n X.J 1 (by simpa using hX.herm) (det_herm hX)
  have hS := Tw.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hco
  have hA := Tw.VacAny.exists_isVac_any_darboux B hB X W r s r' s' hX hW co
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (hA v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hA v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv

end PositivityTheory.ThKG.Tow

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneMain
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure IsEps (σ : E →ₐ[F] E) (B : Base F E) (ε : E) (κ : ℂ) (D : Submodule (𝓞 E) E) {n : ℕ} (X : Spc F E n)
    (r s : ℕ) : Prop where
  herm : ∀ i j, σ (X.J j i) = ε * X.J i j
  sig : ∀ w, HasSig (κ • X.J.map (B.emb w).1) r s
  lat : X.L.IsFullLattice E
  dual : ∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, form σ X.J y x ∈ D
  cartan : ∀ w, IsCartan (κ • X.J.map (B.emb w).1) (X.θ w)
  bas : ∀ v : B.P, IsSplitBasis (B.τ v) X.L (X.bas v)

private theorem full_of_self_dual {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (hcm : IsCMExt F E σ)
    {ε : E} (hεε : ε * ε = 1) (D : Submodule (𝓞 E) E)
    (hherm : ∀ i j, σ (J j i) = ε * J i j)
    (hlat : L.IsLattice E)
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D) :
    L.IsFullLattice E := by
    let := hlat
    refine { span_eq_top := ?_ }
    let W := Submodule.span E (L : Set (Fin n → E))
    change W = ⊤
    by_contra hW
    let g : (Fin n → E) →ₗ[E] Module.Dual E W :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin Jᵀ)).domRestrict₂ W
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin n → E) (hx : x ∈ L) : form σ J y x = 0 := by
      have hz' : z ⬝ᵥ Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      have hzero : form σ J x y = 0 := by
        rw [Matrix.dotProduct_transpose_mulVec] at hz'
        simpa only [form, y, sigma_sigma hcm] using hz'
      have hs := form_swap hcm hherm x y
      rw [hzero, map_zero] at hs
      exact (mul_eq_zero.mp hs.symm).resolve_left (left_ne_zero_of_mul_eq_one hεε)
    have hline (a : E) : a • y ∈ L := (hdual _).2 fun x hx => by
      rw [form_smul_left, horth x hx, mul_zero]
      exact D.zero_mem
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict L hline
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hlat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

theorem exists_plane {B : Base F E} (hB : B.IsGood σ) {ε : E} (hε : ε = 1 ∨ ε = -1) {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) (D : Submodule (𝓞 E) E) (hD1 : (1 : E) ∈ D)
    (hDτ : ∀ v : B.P, ∀ c ∈ D, Valued.v (B.τ v c) ≤ 1) (n n₁ : ℕ) (hn : n = n₁ + 2) (hn₁ : 1 ≤ n₁) (Y : Spc F E n)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hY : IsEps σ B ε κ D Y r s) (i₀ i₁ : ℕ) (h01 : i₀ < i₁) (h1n : i₁ < n) :
    ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsEps σ B ε κ D (GlobalTheory.ThK.reS Y Y') r s ∧
      IsEps σ B ε κ D Y₁ (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  classical
  have hcm : IsCMExt F E σ := hB.cm
  have hκ0 : κ ≠ 0 := left_ne_zero_of_mul_eq_one hκ1
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεL : ∀ a ∈ Y.L, ε • a ∈ Y.L := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have hdet : Y.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine det_ne_zero_of_hasSig (hY.sig w) ?_
    rw [Matrix.det_smul, show (Y.J.map (B.emb w).1).det = (B.emb w).1 Y.J.det from (RingHom.map_det _ _).symm, h0,
      map_zero, mul_zero]
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
    exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance
  have hFull : Y.L.IsFullLattice E := hY.lat
  obtain ⟨x₀, hx₀, hx₀x₀⟩ := exists_isotropic hcm B.emb (by omega) hr hs hdet hε hY.herm hκ0 hκ hY.sig
  obtain ⟨x, y, hxx, hyy, hxy, hL, hP⟩ := exists_adapted_pair hcm hdet hε hY.herm D hD1 Y.L hFull hY.dual θ₀ hθ₀ B.P B.τ
    hDτ x₀ hx₀ hx₀x₀
  have hyx : form σ Y.J y x = ε := by
    have := form_swap hcm hY.herm x y
    rw [hxy, map_one] at this
    linear_combination -ε * this - form σ Y.J y x * hεε
  obtain ⟨ι, P, hPι, horth, hcomp⟩ := exists_compl (σ := σ) n n₁ Y.J x y hn hxx hyy hxy
    (by rw [hyx]; exact left_ne_zero_of_mul_eq_one hεε)
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ ι *ᵥ u ∈ Y.L ∧
      z = s • x + ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨u, hu⟩ := hcomp (z - form σ Y.J z y • x - (ε * form σ Y.J z x) • y) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxx, hyx]
        linear_combination -form σ Y.J z x * hεε) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxy, hyy]; ring)
    have ht : (ε * form σ Y.J z x) • y ∈ Y.L := by rw [mul_smul]; exact hεL _ (hL z hz).1
    refine ⟨_, _, u, (hL z hz).2, ht, ?_, ?_⟩
    · rw [← hu]; exact Y.L.sub_mem (Y.L.sub_mem hz (hL z hz).2) ht
    · rw [← hu]; abel
  set L₁ := Y.L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) with hL₁def
  have hlat₁ : L₁.IsLattice E := by
    apply Submodule.IsLattice.of_fg E
    apply Submodule.fg_of_fg_map_injective _ _ (hY.lat.fg.of_le (Submodule.map_comap_le _ _))
    intro u u' e
    have he := congrArg (P *ᵥ ·) (show ι *ᵥ u = ι *ᵥ u' from e)
    simpa [Matrix.mulVec_mulVec, hPι] using he
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨𝔟, h𝔟⟩ := exists_ideal n Y.L hY.lat.toIsLattice x hx0
  set J₁ := ιᵀ * Y.J * ι.map σ with hJ₁
  have hform₁ : ∀ u u', form σ J₁ u u' = form σ Y.J (ι *ᵥ u) (ι *ᵥ u') := form_gram Y.J ι
  let e : InfinitePlace F → E →+* ℂ := fun w => (B.emb w).1
  have hreal : ∀ w, HasSig (κ • J₁.map (e w)) (r - 1) (s - 1) ∧ ∃ θ θ₁, IsCartan (κ • Y.J.map (e w)) θ ∧
      IsCartan (κ • J₁.map (e w)) θ₁ ∧ θ * ι.map (e w) = ι.map (e w) * θ₁ ∧
      (κ • fun i => e w (y i)) = (2 : ℂ) • θ *ᵥ fun i => e w (x i) := fun w => by
    have cg : (ι.map (e w))ᵀ * (κ • Y.J.map (e w)) * (ι.map (e w)).map star = κ • J₁.map (e w) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm]
    rw [← cg]
    refine real_plane _ _ _ _ (P.map (e w)) hn (map_herm hcm _ (hκ _) hY.herm) ?_ ?_ ?_ ?_ ?_ ?_ (hY.sig w)
    · rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hxx, map_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hyy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hxy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J ι x (fun u => (horth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J ι y (fun u => (horth u).2), smul_zero, smul_zero]
    · rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  choose hsig₁ θ θ₁ hθ hθ₁ hθι hθx using hreal
  have hherm₁ : ∀ i j, σ (J₁ j i) = ε * J₁ i j := by
    intro i j
    rw [← form_single (σ := σ) J₁ j i, ← form_single (σ := σ) J₁ i j, hform₁, hform₁,
      form_swap hcm hY.herm]
  have hdual₁ : ∀ u, u ∈ L₁ ↔ ∀ u' ∈ L₁, form σ J₁ u u' ∈ D := by
    intro u
    refine ⟨fun hu u' hu' => ?_, fun H => ?_⟩
    · rw [hform₁]; exact (hY.dual _).1 hu _ hu'
    · show ι *ᵥ u ∈ Y.L
      refine (hY.dual _).2 fun z hz => ?_
      obtain ⟨_, _, u', -, -, hu', hz'⟩ := hsplit z hz
      rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1,
        (horth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform₁]
      exact H u' hu'
  haveI hfull₁ : L₁.IsFullLattice E := full_of_self_dual J₁ L₁ hcm hεε D hherm₁ hlat₁ hdual₁
  have hb₁ : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) L₁ β := fun v => exists_isSplitBasis (B.τ v) L₁ hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : Pl F, GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  choose β hβ using fun v : B.P => exists_basis (B.τ v) n n₁ Y.L x y ι (β₁ v) i₀ i₁ hn h01 h1n hFull hsplit
    (hP v).1 (hP v).2 (hβ₁ v)
  let bas : ∀ v : Pl F, GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y₁ : Spc F E n₁ := ⟨J₁, L₁, θ₁, bas₁⟩
  let Y' : Spc F E n := ⟨Y.J, Y.L, θ, bas⟩
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact { herm := hY.herm, sig := hY.sig, lat := hY.lat, dual := hY.dual, cartan := hθ
            bas := fun v => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v]
              exact (hβ v).2 }
  · exact { herm := hherm₁
            sig := hsig₁
            lat := hfull₁
            dual := hdual₁
            cartan := hθ₁
            bas := fun v => by
              rw [show Y₁.bas v = β₁ v from hbas₁ v]
              exact hβ₁ v }
  · exact { rank := hn, xx := hxx, yy := hyy, xy := hxy, orth := horth, gram := rfl, low := fun u => Iff.rfl
            split := hsplit
            ideal := h𝔟
            cartan := fun w => ⟨hθι w, κ⁻¹ * 2, mul_ne_zero (inv_ne_zero hκ0) two_ne_zero, by
              rw [mul_smul]
              exact (eq_inv_smul_iff₀ hκ0).2 (hθx w)⟩
            bas := fun v i => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show Y₁.bas v = β₁ v from hbas₁ v]
              exact (hβ v).1 i }

theorem isHerm_iff {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} : X.IsHerm σ B r s ↔ IsEps σ B 1 1 (intE E) X r s :=
  ⟨fun h => ⟨by simpa using h.herm, by simpa using h.sig, h.lat, h.dual, by simpa using h.cartan, h.bas⟩,
    fun h => ⟨by simpa using h.herm, by simpa using h.sig, h.lat, h.dual, by simpa using h.cartan, h.bas⟩⟩

theorem isSkew_iff {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} :
    X.IsSkew σ B r s ↔ IsEps σ B (-1) Complex.I (codE E) X r s :=
  ⟨fun h => ⟨by simpa using h.skew, h.sig, h.lat, h.dual, h.cartan, h.bas⟩,
    fun h => ⟨by simpa using h.herm, h.sig, h.lat, h.dual, h.cartan, h.bas⟩⟩

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.StabEx
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem stabEx : StabEx := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  obtain ⟨μK, hμK⟩ := Stab.exists_haar_of_isCompact (Stab.stabK (σ := σ) B X) (Stab.isCompact_stabK hB hX)
  obtain ⟨μ, hμ⟩ := Stab.exists_haar_idele (F := F) (E := E)
  exact ⟨_, μK, μ, Stab.isStab_stabK B X, Stab.isCompact_stabK hB hX, hμK, hμ⟩

end PositivityTheory.ThKG.Tow

end
end

