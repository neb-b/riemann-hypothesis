module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyLiftObj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LpUnrNegOneSpec
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

section

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

abbrev WDAt (N : NData R H what₂) (w : PlE H) : Type :=
  WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

abbrev UnrWDFam (N : NData R H what₂) (a : ℕ) : Type :=
  {p : (∀ w, WDAt N w) × ((H.E →+* ℂ) → Multiset ℂ) //
    (∀ w, (p.1 w).unr ∧ (p.1 w).lpDim = a) ∧ ∀ τ, Multiset.card (p.2 τ) = a}

theorem lpUnr_negOne_spec (N : NData R H what₂) (w : PlE H) :
    (WD.lpUnr (h := N.plOm.2 w) {-1}).unr ∧
      (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig = {-1} ∧
      (WD.lpUnr (h := N.plOm.2 w) {-1}).lpDim = 1 := by
  obtain ⟨hu, he, hd⟩ := WD.lpUnr_spec (h := N.plOm.2 w) ({-1} : Multiset ℂ) (by simp)
  exact ⟨hu, he, hd.trans (Multiset.card_singleton _)⟩

def negOneWDFam (N : NData R H what₂) : UnrWDFam N 1 :=
  ⟨(fun w => WD.lpUnr (h := N.plOm.2 w) {-1}, fun _ => {0}),
    fun w => ⟨(lpUnr_negOne_spec N w).1, (lpUnr_negOne_spec N w).2.2⟩, fun _ => rfl⟩

theorem UnrWDFam.exists_frobEig {N : NData R H what₂} (χ : UnrWDFam N 1) (w : PlE H) :
    ∃ c, (χ.1.1 w).frobEig = {c} := by
  have hu : (χ.1.1 w).unr := (χ.2.1 w).1
  have hd : (χ.1.1 w).lpDim = 1 := (χ.2.1 w).2
  have hc : Multiset.card (χ.1.1 w).frobEig = 1 := ((WD.unramified_laws (N.plOm.2 w)).2.2.2.2.2.2.2.2.2.2.2.2.1 _ hu).trans hd
  exact Multiset.card_eq_one.mp hc


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def nAutWD (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) : NAut N where
  LP := WDAt N
  lpDim := WD.lpDim
  lpZero := fun w => WD.lpZero (h := N.plOm.2 w)
  lpSum := WD.lpSum
  lpTw := WD.lpTw
  lpChar := WD.lpChar
  lpUnr := fun w => WD.lpUnr (h := N.plOm.2 w)
  mono0 := WD.mono0
  unr := WD.unr
  frobEig := WD.frobEig
  tempered := WD.tempered
  inePol := WD.inePol
  items₂ := fun k w a => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab (τ k) (γ k w) a
  lpDim_zero := fun w => WD.lpDim_zero _
  lpDim_sum := WD.lpDim_sum
  lpDim_tw := WD.lpDim_tw
  lpUnr_spec := fun _ => WD.lpUnr_spec
  unr_sum := WD.unr_sum
  monomial_sum_iff := WD.monomial_sum_iff
  frobEig_sum := fun a b _ _ => WD.frobEig_lpSum a b
  unr_tw := WD.unr_tw
  monomial_twist_iff := WD.monomial_twist_iff
  frobEig_tw := WD.frobEig_tw
  frobEig_char := fun a χ c ha hχ _ => WD.frobEig_char a χ c ha hχ
  lpDim_char := WD.lpDim_char
  unr_char := fun a χ _ => WD.unr_lpChar a χ
  monomial_char_iff := WD.monomial_char_iff
  lpZero_unr := fun _ => WD.lpZero_unr
  frobEig_zero := fun _ => WD.frobEig_zero
  lpSum_zero := WD.lpSum_zero
  lpSum_comm := WD.lpSum_comm
  lpSum_assoc := WD.lpSum_assoc
  lpTw_zero := WD.lpTw_zero
  lpTw_add := WD.lpTw_add
  lpTw_sum := WD.lpTw_sum
  unr_eq_lpUnr := WD.unr_eq_lpUnr
  unr_mono0 := WD.unr_mono0
  frobEig_ne_zero := WD.frobEig_ne_zero
  frobEig_card := fun a _ => WD.card_eig a _
  tempered_unr := WD.tempered_unr
  inePol_sum := WD.inePol_sum
  inePol_tw := WD.inePol_tw
  unr_iff_ine := WD.unr_iff_ine
  inertiaCharpoly_zero := fun k w => by
    let : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    have hzero := WD.lpDim_zero (N.plOm.2 w)
    exact WD.lab_of_lpDim_eq_zero (τ k) (γ k w) hzero
  inertiaCharpoly_add := fun k _ a b => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab_lpSum _ _ a b
  CG := UnrWDFam N
  csd := fun π => ∀ w w', IsConjPl H w w' → (π.1.1 w').frobEig = (π.1.1 w).frobEig.map (·⁻¹)
  ralg := fun {a} π => ∀ τ, (π.1.2 τ).Nodup ∧ ∀ z ∈ π.1.2 τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  locG := fun π w => π.1.1 w
  locG_dim := fun π w => (π.2.1 w).2
  locG_unr_ae := fun π => Filter.Eventually.of_forall fun w => (π.2.1 w).1
  tw := fun π χ => ⟨(fun w => (π.1.1 w).lpChar (χ.1.1 w), fun τ => (π.1.2 τ).map (· + (χ.1.2 τ).sum)),
    fun w => ⟨WD.unr_lpChar _ _ (π.2.1 w).1 (χ.2.1 w).1, (WD.lpDim_char _ _ (χ.2.1 w).2).trans (π.2.1 w).2⟩,
    fun τ => (Multiset.card_map _ _).trans (π.2.2 τ)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun π τ => π.1.2 τ
  infG_card := fun π τ => π.2.2 τ
  ralg_def := fun _ => Iff.rfl
  infG_tw := fun π χ τ s h => by
    show (π.1.2 τ).map (· + (χ.1.2 τ).sum) = _
    rw [show χ.1.2 τ = {s} from h, Multiset.sum_singleton]
  csd_tw := fun π χ hχ hπ w w' h => by
    obtain ⟨c, hc⟩ := χ.exists_frobEig w
    have hc' := hχ w w' h
    rw [hc, Multiset.map_singleton] at hc'
    show ((π.1.1 w').lpChar (χ.1.1 w')).frobEig = ((π.1.1 w).lpChar (χ.1.1 w)).frobEig.map (·⁻¹)
    rw [WD.frobEig_char _ _ _ (π.2.1 w').1 (χ.2.1 w').1 hc', WD.frobEig_char _ _ _ (π.2.1 w).1 (χ.2.1 w).1 hc,
      hπ w w' h, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => (mul_inv _ _).symm
  csd_unr := fun π w w' h hc _ => ⟨(π.2.1 w').1, h w w' hc⟩
  etaT := negOneWDFam N
  etaTinv := negOneWDFam N
  etaT_unr := fun w => (lpUnr_negOne_spec N w).1
  etaT_inert := fun w _ => (lpUnr_negOne_spec N w).2.1
  etaTinv_def := fun w => ⟨(lpUnr_negOne_spec N w).1, by
    show (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig =
      (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig.map (·⁻¹)
    rw [(lpUnr_negOne_spec N w).2.1]
    simp⟩
  etaT_split := fun w w' _ _ a b ha hb => by
    have ha' : (-1 : ℂ) = a := Multiset.singleton_inj.1 ((lpUnr_negOne_spec N w).2.1.symm.trans ha)
    have hb' : (-1 : ℂ) = b := Multiset.singleton_inj.1 ((lpUnr_negOne_spec N w').2.1.symm.trans hb)
    rw [← ha', ← hb']
    norm_num
  plGw := pl
  plGw_over := h1
  plGw_inj := h2
  plGw_nconj := h3
  iotaQ := fun i => hE.elim i
  iotaQC := fun i => hE.elim i
  iota_LL := fun i => hE.elim i
  iotaQ_alg := fun i => hE.elim i
  muC := fun i => hE.elim i
  muC_csd := fun i => hE.elim i
  AV := fun i => hE.elim i
  finAV := fun i => hE.elim i
  ptV := fun i => hE.elim i
  typeV := fun i => hE.elim i
  typeV_ne := fun i => hE.elim i
  typeV_indep := fun i => hE.elim i
  typeV_top := fun i => hE.elim i
  pt_surj := fun i => hE.elim i
  eig_dim := fun i => hE.elim i
  locV := fun i => hE.elim i
  satV := fun i => hE.elim i
  locV_unr := fun i => hE.elim i
  pt_loc := fun i => hE.elim i
  infWt := fun i => hE.elim i
  locW := fun i => hE.elim i
  satW := fun i => hE.elim i
  lab_loc := fun i => hE.elim i
  wdOf := fun i => hE.elim i
  wdOf_dim := fun i => hE.elim i
  wdOf_unr := fun i => hE.elim i
  wdOf_frob := fun i => hE.elim i
  wdOf_ine := fun i => hE.elim i
  wdOf_mono0 := fun i => hE.elim i
  IsCrysW := fun i => hE.elim i
  IsPotCrysW := fun i => hE.elim i
  IsdRW := fun i => hE.elim i
  jumpsW := fun i => hE.elim i
  wdOf_unrL := fun i => hE.elim i
  wdOf_mono0L := fun i => hE.elim i
  jumpsInf := fun i => hE.elim i
  locAutHodgeTateWeightsLevelZero := fun i => hE.elim i
  jumpsInf_def := fun i => hE.elim i
  locAut_hodgeTateWeightsLevelZero_def := fun i => hE.elim i
  chi_mu := fun i => hE.elim i
  kFbar := fun i => hE.elim i

def wdTieWD (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) :
    GlobalTheory.RowTie.WDTie N (nAutWD N hE pl h1 h2 h3 τ γ) :=
  ⟨fun _ => Equiv.refl _, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => rfl⟩

end

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiCComp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.FormSym

theorem mem_FiC_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n)
    {c c' : Type} (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (e : c' → c) (he : Function.Surjective e)
    (g : c → Frames (gramC J emb) → ℂ) :
    g ∘ e ∈ FiC S emb lam (yc ∘ e) ↔ g ∈ FiC S emb lam yc := by
  simp only [FiC, Submodule.mem_map]
  constructor
  · rintro ⟨h, hh, he'⟩
    refine ⟨h, hh, ?_⟩
    funext x
    obtain ⟨x', rfl⟩ := he x
    exact congrFun he' x'
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

section Gen

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}

def clsOfChart (β : Ch) (hβ : ∀ c, chOf c = β)
    (K : LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) : ClsTied u i hi where
  lev := K.lev
  y c := K.y ⟨c, hβ c⟩
  y_bij := K.y_bij.comp (f := fun c : (D.mem u).C.cls i => (⟨c, hβ c⟩ : {c // chOf c = β}))
    ⟨fun _ _ h => congrArg Subtype.val h, fun c => ⟨c.1, rfl⟩⟩
  y_lat c := K.y_lat ⟨c, hβ c⟩
  stabI c := K.stabI ⟨c, hβ c⟩
  stabI_inj c := K.stabI_inj ⟨c, hβ c⟩
  stabI_range c := K.stabI_range ⟨c, hβ c⟩


set_option maxHeartbeats 4000000 in
def valOfG [Subsingleton Ch] (eV : (D.mem u).A.vT ≃ PlT D u)
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)
    (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (hde : ∃ C : GL (Fin (D.R.N i)) D.host.E,
      cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
      (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eY z).1 τ).det)
    (hV : ValuationCompatibleChart (D.fm u) eY (fun _ => True) chOf (lat := fun c => clsCrd D u i hi c) K)
    (hI : IpVTieG (D.fm u) eY)
    (hD : DilationCompatibleChart (D.fm u) eY eV chOf (lat := fun c => clsCrd D u i hi c) K) :
    ValTied u eV i hi (clsOfChart β hβ (K β)) where
  eY := eY
  de := hde
  Fi φ := by
    rw [hV.Fi φ]
    constructor
    · intro h
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).2 (h β)
    · intro h β'
      obtain rfl : β = β' := Subsingleton.elim _ _
      exact (mem_FiC_comp _ _ _ (K β).y (fun c => (⟨c, hβ c⟩ : {c // chOf c = β})) (fun c => ⟨c.1, rfl⟩) _).1 h
  ipV := hI
  rat := hV.rat
  lat x := by
    constructor
    · intro hx w
      exact (hV.lat w trivial x).1 (Submodule.subset_span hx)
    · intro h
      exact GlobalTheory.LvT.mem_of_forall_locW D _ (fun w => (hV.lat w trivial x).2 (h w))
  dil v a k hk c δ hδ := hD.dil v a k hk β ⟨c, hβ c⟩ δ hδ
  dilT v a k hk c δ hδ g hg := hD.dilT v a k hk β ⟨c, hβ c⟩ δ hδ g hg


set_option maxHeartbeats 4000000 in
def lvOfG (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c)) :
    LvTied u A i hi where
  pr := L.pr
  pr_surj := L.pr_surj
  pr_smul := L.pr_smul
  pr_ker := L.pr_ker
  fv_ker := L.fv_ker
  prk := L.prk
  prk_surj := L.prk_surj
  prk_smul := L.prk_smul
  prk_ker := L.prk_ker
  te := L.te

variable (A : AtTTied u) (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T A.res i hi (fun c => clsCrd D u i hi c))
  (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1)) (β : Ch) (hβ : ∀ c, chOf c = β)

set_option maxHeartbeats 4000000 in
theorem fvOfG (fMe : ∀ β v, (K β).lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (h : FvTieG L A.eV K fMe) :
    FvTie (lvOfG A L) (clsOfChart β hβ (K β)) (fMe β) :=
  fun v c z hz => h v β ⟨c, hβ c⟩ z hz

set_option maxHeartbeats 4000000 in
theorem upOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : UpNatTieG L eY A.eV K) : UpNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c z hz
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h v β ⟨c, hβ c⟩ z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 g s s' hs

set_option maxHeartbeats 4000000 in
theorem dnOfG (eY : (D.mem u).C.Y i ≃ Fr D i hi) (W : ValTied u A.eV i hi (clsOfChart β hβ (K β))) (hY : W.eY = eY)
    (h : DnNatTieG L eY A.eV K) : DnNatTie (lvOfG A L) (clsOfChart β hβ (K β)) W := by
  intro v c g hg
  obtain ⟨_, γ, η, κ, h1, h2, h3, h4, h6⟩ := h v β ⟨c, hβ c⟩ g hg
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun f s s' hs => ?_⟩
  rw [hY] at hs
  exact h6 f s s' hs

end Gen

section Gen2

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 4000000 in
theorem normOfG {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u eV i hi K) (hY : W.eY = eY) (h : NormTieG (D.fm u) eY) : NormTie W := by
  intro s x Pc hPc o ho
  rw [hY] at hPc
  exact h s x Pc hPc o ho

set_option maxHeartbeats 4000000 in
theorem bwOfG (A : AtTTied u) {K : ClsTied u i hi} (eY : (D.mem u).C.Y i ≃ Fr D i hi)
    (W : ValTied u A.eV i hi K) (hY : W.eY = eY)
    (h : BwTieG (D.fm u) (D.mem u).A.T A.res eY (fun c => clsCrd D u i hi c)) : BwTie A W := by
  intro w hw hs v x
  rw [hY]
  exact h w hw hs v x

end Gen2


set_option maxHeartbeats 4000000 in
theorem readsK_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {u : B.Word} {a : I.ι}
    {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))} (h : I.ReadsK l Z u a i hi chOf K) (β : Ch)
    (hβ : ∀ c, chOf c = β) :
    ∃ k, I.Reads u a i (fun _ => ()) (fun _ => (K β).lev.Lb) (fun _ => (K β).lev.U) (fun _ => (K β).lev.chi)
      (fun c => ((K β).y ⟨c, hβ c⟩).1) (fun c s => ((K β).stabI ⟨c, hβ c⟩ s).1) k := by
  obtain rfl : chOf = fun _ => β := funext hβ
  obtain ⟨k, hk⟩ := h
  refine ⟨fun _ => k β, ⟨fun c c' => ⟨fun _ => (hk.key c c').1 rfl, fun _ => rfl⟩, fun _ => ?_, fun _ => hk.lb β,
    fun _ => hk.k_std β, fun _ => hk.k_off β, fun _ => hk.k_T β, hk.pt, hk.lev, hk.chr, hk.stab⟩⟩
  obtain ⟨c, _⟩ := hk.onto β
  exact ⟨c, rfl⟩

end GlobalTheory.Mem.FormSym

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def latSD (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : (letI := B.host.cmStar; SDLat B.host.E (B.R.N i)) :=
  letI := B.host.cmStar
  ⟨((I.stp u a i).rep c).1.1.deco.1.N, GlobalTheory.SeamSelfDual.isSDLat_of_isSdLat _
    ⟨((I.stp u a i).rep c).1.1.deco.2.lat, ((I.stp u a i).rep c).1.1.deco.2.uni⟩⟩

def mtOf (a : I.ι) (j : ℕ) : (I.rec7 l Z).Dt →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ B.R.m then
    (I.rec7 l Z).muTil j * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) else (I.rec7 l Z).muTil j

theorem mtOf_factors (u : B.Word) (a : I.ι) : GL3Theta.CarriesTupleCharacters (I.rec7 l Z) ((I.rec7 l Z).chTw u a) (I.mtOf l Z a)
    (fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1) := by
  intro i hi
  have hm : 1 ≤ i + 1 ∧ i + 1 ≤ B.R.m := ⟨by omega, hi⟩
  refine ⟨fun c => ?_, fun c => ?_⟩
  · show ((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt_eq]
    simp only [GL3Theta.rhoOf, mtOf, if_pos hm]
    rfl
  · show ((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt'_eq]
    simp only [GL3Theta.rhoOf', mtOf, if_pos hm]
    rfl

def objOf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a) :=
  letI := B.host.cmStar
  { mt := I.mtOf l Z a
    L0 := fun i => ⟨GlobalTheory.Glob.IntegralWittCoefficients.Model.stdLat _ _, GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _⟩
    lattice_integral_coordinates := fun i x => GlobalTheory.Glob.IntegralWittCoefficients.Model.mem_stdLat x
    lat := fun i c => I.latSD u a i c
    dt := fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1
    dt_lat := fun i c => GlobalTheory.Mem.Col2.mk_detPt_eq_relDetQ B.R B.host _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1
    c13 := I.mtOf_factors l Z u a
    frm := fun i y => y.1
    frm_inj := fun i _ => Subtype.val_injective
    frm_range := fun i _ f => ⟨by
        rintro ⟨y, rfl⟩ τ
        exact (y.2 τ).ne_zero, fun h => ⟨⟨f, fun τ => isUnit_iff_ne_zero.2 (h τ)⟩, rfl⟩⟩
    frm_de := fun _ _ _ _ => rfl
    dgen := I.J.cD
    dgen_gen := hok.amb_ok.dgen
    S := insert (B.T u) ({B.host.g 0, B.host.g 1} ∪ Qp a)
    Th := fun i c c' => I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') }

theorem objOf_unf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) :
    UnfIsAll (I.objOf l Z hok Qp u a) i := by
  intro c c' Q
  have e0 : ∀ (n : ℕ) (P : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N n)) ℂ),
      frPoly (I.objOf l Z hok Qp u a) n P = fnOf (Gr B.fields.emb B.embLL (B.R.N n)) 0 1 P := by
    intro n P
    funext y
    simp [frPoly, GL3Theta.evFr, fnOf, objOf]
    rfl
  have e1 : frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    LinearMap.congr_fun (frInv_spec (I.objOf l Z hok Qp u a) hi) Q
  show fnOf _ 0 1 (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 _ _)) 0 (polOf _ 0 (fr0 _ _ _) (frPoly (I.objOf l Z hok Qp u a) i Q))) =
    frPoly (I.objOf l Z hok Qp u a) (i + 1) (jetMap _ _ (frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q)))
  have e2 : polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))
      (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    (congrArg _ (e0 i Q)).trans (GlobalTheory.TilClass.polOf_fnOf_one B.fields.emb B.embLL 0 Q)
  refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1
    (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) 0 P)) e2).trans ?_
  rw [e1, e0 (i + 1)]
  rfl

theorem lift_objects : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ Qp : I.ι → Finset ℕ, ∃ O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a), I.StdO l Z Qp O ∧ ∀ u a i, i < B.R.m → UnfIsAll (O u a) i := by
  intro B X I hok _ l Z Qp
  refine ⟨I.objOf l Z hok Qp, ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩, fun u a i hi => I.objOf_unf l Z hok Qp u a i hi.le⟩

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetAutSelfNaut
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

def RowWD.unram (D : D7) (m : D.what₂.FT → PlE D.host → Multiset ℂ) (h0 : ∀ σ w, (0:ℂ) ∉ m σ w)
    (hc : ∀ σ w, Multiset.card (m σ w) = D.R.r) : RowWD D where
  par σ w := WD.lpUnr (D.nd.plOm.2 w) (m σ w)
  sat := m
  dim σ w := (WD.lpUnr_spec (h := D.nd.plOm.2 w) (m σ w) (h0 σ w)).2.2.trans (hc σ w)
  tame σ k v :=
    let w := D.naut.plGw k v
    WD.tame_of_unr (WD.lpUnr_spec (h := D.nd.plOm.2 w) (m σ w) (h0 σ w)).1

end GlobalTheory.HeightCounting
end
end

