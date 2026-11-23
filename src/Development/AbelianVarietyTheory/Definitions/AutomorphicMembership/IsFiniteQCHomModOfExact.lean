module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0514
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC structureModule)
open GlobalTheory.VB GlobalTheory.PtNorm

namespace GlobalTheory.PtNorm

variable {X : Scheme.{0}} {F G : X.Modules} {U : X.Opens} {p : ℕ} {C : SCF p} (z : Sp (intO C.S) ⟶ X) (hp : p ≠ 0)


section Coherent

variable {X : Scheme.{0}} {P Q F G : X.Modules}

theorem sec_ext_affine {W : X.Opens} {a b : Γ(G, W)}
    (e : ∀ (T : X.Opens) (h : T ≤ W), IsAffineOpen T → resM G h a = resM G h b) : a = b :=
  GlobalTheory.Twist.sec_ext_of_cover (fun T : {T : X.Opens // IsAffineOpen T ∧ T ≤ W} => T.1) (fun T => T.2.2)
    (fun x hx => by
      obtain ⟨T, hT, hxT, hle⟩ := QCoh.exists_affine_mem_le (U := W) x hx
      exact Opens.mem_iSup.2 ⟨⟨T, hT, hle⟩, hxT⟩) fun T => e T.1 T.2.2 T.2.1

theorem exists_hom_of_exact (φ : Q ⟶ P) (π : P ⟶ F)
    (hex : ∀ T : X.Opens, IsAffineOpen T → Function.Exact (φ.app T) (π.app T))
    (hs : ∀ T : X.Opens, IsAffineOpen T → Function.Surjective (π.app T)) {U : X.Opens}
    (ψ : Γ(homMod P G, U)) (hψ : ∀ (W : X.Opens) (h : W ≤ U) (m : Γ(Q, W)), homApp ψ h (φ.app W m) = 0) :
    ∃ χ : Γ(homMod F G, U), (homMap π (𝟙 G)).app U χ = ψ := by
  have wd (T : X.Opens) (hT : IsAffineOpen T) (h : T ≤ U) (m m' : Γ(P, T))
      (e : π.app T m = π.app T m') : homApp ψ h m = homApp ψ h m' := by
    obtain ⟨q, hq⟩ := (hex T hT (m - m')).1 (by rw [map_sub, e, sub_self])
    rw [← sub_eq_zero, ← map_sub, ← hq, hψ]
  have H (W : X.Opens) (h : W ≤ U) (s : Γ(F, W)) : ∃ t : Γ(G, W), ∀ (T : X.Opens) (h' : T ≤ W),
      IsAffineOpen T → ∀ m : Γ(P, T), π.app T m = resM _ h' s → resM G h' t = homApp ψ (h'.trans h) m := by
    choose m hm using fun T : {T : X.Opens // IsAffineOpen T ∧ T ≤ W} =>
      hs T.1 T.2.1 (resM _ T.2.2 s)
    obtain ⟨t, ht⟩ := GlobalTheory.Twist.exists_sec_of_cover (fun T : {T : X.Opens // IsAffineOpen T ∧ T ≤ W} => T.1)
      (fun T => T.2.2) (fun x hx => by
        obtain ⟨T, hT, hxT, hle⟩ := QCoh.exists_affine_mem_le (U := W) x hx
        exact Opens.mem_iSup.2 ⟨⟨T, hT, hle⟩, hxT⟩) (fun T => homApp ψ (T.2.2.trans h) (m T)) fun T T' =>
      sec_ext_affine fun V hV hA => by
        rw [resM_resM, resM_resM, ← homApp_resM, ← homApp_resM]
        exact wd V hA _ _ _ (by rw [app_resM, app_resM, hm, hm, resM_resM, resM_resM])
    exact ⟨t, fun T h' hT n hn => (ht ⟨T, hT, h'⟩).trans (wd T hT _ _ _ ((hm ⟨T, hT, h'⟩).trans hn.symm))⟩
  choose t ht using H
  refine ⟨homMk (fun W h =>
    { toFun := t W h
      map_add' a b := sec_ext_affine fun T h' hT => ?_
      map_smul' a b := sec_ext_affine fun T h' hT => ?_ }) fun W W' h h' s => sec_ext_affine fun T h'' hT => ?_,
    VB.hom_ext fun W h m => sec_ext_affine fun T h' hT => ?_⟩
  · obtain ⟨m, hm⟩ := hs T hT (resM _ h' a)
    obtain ⟨n, hn⟩ := hs T hT (resM _ h' b)
    rw [map_add (f := _), ht W h a T h' hT m hm, ht W h b T h' hT n hn,
      ht W h _ T h' hT (m + n) (by rw [map_add (f := _), map_add (f := _), hm, hn]), map_add (f := _)]
  · obtain ⟨n, hn⟩ := hs T hT (resM _ h' b)
    rw [RingHom.id_apply, resM_smul, ht W h b T h' hT n hn,
      ht W h _ T h' hT (_ • n) (by rw [resM_smul, ← hn, Scheme.Modules.Hom.app_smul]), map_smul]
  · obtain ⟨n, hn⟩ := hs T hT (resM _ (h''.trans h') s)
    change resM G h'' (t W' _ _) = resM G h'' (resM G h' (t W h s))
    rw [resM_resM, ht W h s T _ hT n hn, ht W' _ _ T h'' hT n (by rw [hn, resM_resM])]
  · exact (ht W h _ T h' hT (resM P h' m) (app_resM _ _ _)).trans (homApp_resM ψ h h' m)

theorem isFiniteQC_homMod_of_exact [IsLocallyNoetherian X] {r r' : ℕ} (hQ : IsVB Q r') (hP : IsVB P r) (φ : Q ⟶ P)
    (π : P ⟶ F) (hex : ∀ T : X.Opens, IsAffineOpen T → Function.Exact (φ.app T) (π.app T))
    (hs : ∀ T : X.Opens, IsAffineOpen T → Function.Surjective (π.app T)) (w : φ ≫ π = 0) [IsFiniteQC G] :
    IsFiniteQC (homMod F G) := by
  have h₁ : IsFiniteQC (homMod P G) := isFiniteQC_homMod hP
  have h₂ : IsFiniteQC (homMod Q G) := isFiniteQC_homMod hQ
  have h₃ := h₁.isQuasicoherent
  have h₄ := h₂.isQuasicoherent
  have hι (U : X.Opens) : Function.Injective ((homMap π (𝟙 G)).app U) := fun χ χ' e =>
    VB.hom_ext fun W h s => sec_ext_affine fun T h' hT => by
      obtain ⟨m, hm⟩ := hs T hT (resM _ h' s)
      have e' := congrArg (fun ψ : Γ(homMod P G, U) => homApp ψ (h'.trans h) m) e
      rw [← homApp_resM, ← homApp_resM, ← hm]
      exact e'
  have hex' (U : X.Opens) : Function.Exact ((homMap π (𝟙 G)).app U) ((homMap φ (𝟙 G)).app U) := fun ψ => by
    refine ⟨fun h => exists_hom_of_exact φ π hex hs ψ fun W hW m => ?_, ?_⟩
    · exact congrArg (fun ψ : Γ(homMod Q G, U) => homApp ψ hW m) h
    · rintro ⟨χ, rfl⟩
      refine VB.hom_ext fun W h m => ?_
      rw [homApp_homMap, homApp_homMap, QCoh.app_app φ π, w]
      exact map_zero (homApp χ h)
  have : (homMod F G).IsQuasicoherent :=
    QCoh.isQuasicoherent_of_exact_app (homMap π (𝟙 G)) (homMap φ (𝟙 G)) (fun U _ => hι U) fun U _ => hex' U
  refine .of_forall_exists_affine fun x => ?_
  obtain ⟨U, hU, hx⟩ := QCoh.exists_affine_mem x
  have := QCoh.isNoetherian_sections (homMod P G) hU
  exact ⟨U, hU, hx, Module.Finite.of_injective (QCoh.appLinear (homMap π (𝟙 G)) U) (hι U)⟩

theorem isFiniteQC_homMod_cokernel [IsLocallyNoetherian X] {r r' : ℕ} (hQ : IsVB Q r') (hP : IsVB P r) (φ : Q ⟶ P)
    [IsFiniteQC G] : IsFiniteQC (homMod (cokernel φ) G) :=
  have := hQ.isQuasicoherent
  have := hP.isQuasicoherent
  isFiniteQC_homMod_of_exact hQ hP φ (cokernel.π φ) (fun _ hT => QCoh.exact_cokernel_π_app φ hT)
    (fun _ hT => QCoh.surjective_cokernel_π_app φ hT) (cokernel.condition φ)


end Coherent

end GlobalTheory.PtNorm

namespace GlobalTheory.LocM

section Reduction

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

abbrev modN (F : 𝒜) (n : ℕ) : 𝒜 := cokernel (n • 𝟙 F)

def modNRed (F : 𝒜) {n m : ℕ} (h : n ∣ m) : modN F m ⟶ modN F n :=
  cokernel.desc _ (cokernel.π _) (by
    obtain ⟨c, rfl⟩ := h
    rw [mul_comm, mul_smul, Preadditive.nsmul_comp, cokernel.condition, smul_zero])

@[reassoc (attr := simp)] theorem π_modNRed (F : 𝒜) {n m : ℕ} (h : n ∣ m) :
    cokernel.π (m • 𝟙 F) ≫ modNRed F h = cokernel.π (n • 𝟙 F) := cokernel.π_desc _ _ _

theorem nsmul_id_modN (F : 𝒜) (n : ℕ) : n • 𝟙 (modN F n) = 0 := by
  rw [← cancel_epi (cokernel.π (n • 𝟙 F)), Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  simpa only [Preadditive.nsmul_comp, Category.id_comp] using cokernel.condition (n • 𝟙 F)

def redMap {F G : 𝒜} {n m : ℕ} (h : n ∣ m) (φ : modN F m ⟶ modN G m) : modN F n ⟶ modN G n :=
  cokernel.desc (n • 𝟙 F) (cokernel.π (m • 𝟙 F) ≫ φ ≫ modNRed G h) (by
    rw [Preadditive.nsmul_comp, Category.id_comp, ← Category.comp_id (cokernel.π _ ≫ φ ≫ modNRed G h),
      ← Preadditive.comp_nsmul, nsmul_id_modN, comp_zero])

theorem modNRed_redMap {F G : 𝒜} {n m : ℕ} (h : n ∣ m) (φ : modN F m ⟶ modN G m) :
    modNRed F h ≫ redMap h φ = φ ≫ modNRed G h := by
  rw [← cancel_epi (cokernel.π (m • 𝟙 F)), π_modNRed_assoc, redMap, cokernel.π_desc]

instance epi_modNRed (F : 𝒜) {n m : ℕ} (h : n ∣ m) : Epi (modNRed F h) :=
  epi_of_epi_fac (π_modNRed F h)

def modNMap {F G : 𝒜} (φ : F ⟶ G) (n : ℕ) : modN F n ⟶ modN G n :=
  cokernel.map _ _ φ φ (by rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id])

@[reassoc (attr := simp)] theorem π_modNMap {F G : 𝒜} (φ : F ⟶ G) (n : ℕ) :
    cokernel.π (n • 𝟙 F) ≫ modNMap φ n = φ ≫ cokernel.π (n • 𝟙 G) := cokernel.π_desc _ _ _

@[simp] theorem redMap_modNMap {F G : 𝒜} {n m : ℕ} (h : n ∣ m) (φ : F ⟶ G) : redMap h (modNMap φ m) = modNMap φ n := by
  rw [← cancel_epi (modNRed F h), modNRed_redMap, ← cancel_epi (cokernel.π (m • 𝟙 F))]
  simp

theorem exists_shortExact_congr {F G H : 𝒜} {f f' : F ⟶ G} {g g' : G ⟶ H} (hf : f = f') (hg : g = g') :
    (∃ w : f ≫ g = 0, (ShortComplex.mk _ _ w).ShortExact) ↔ ∃ w : f' ≫ g' = 0, (ShortComplex.mk _ _ w).ShortExact := by
  subst hf hg
  rfl

end Reduction

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p) {Z : ct.Mdl}

theorem isVB_free (Z : ct.Mdl) (a m : ℕ) : IsVB (Z.free a m) m :=
  (isVB_freeModule_fin Z.X m).twist (LB.isLB_pull (GlobalTheory.ProjSpace.On_isLB _ _ _) _)

instance isFiniteQC_toMod (F : ct.Sh Z) : IsFiniteQC F.toMod :=
  have := (ct.isVB_free Z F.a F.m).isFiniteQC
  have := (ct.isVB_free Z F.a' F.m').isQuasicoherent
  QCoh.isFiniteQC_cokernel F.φ

def presIso (F : Z.X.Modules) [IsFiniteQC F] : (Z.ofMod F).toMod ≅ F :=
  (GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ Z F).some

theorem nrm_ofMod (F : Z.X.Modules) [IsFiniteQC F] (f : Γ(F, Z.genO)) (y : ct.Pt Z) :
    ct.nrm (Z.ofMod F) ((ct.presIso F).inv.app _ f) y = sSup (nrmSet y.z F f) :=
  congrArg sSup (nrmSet_iso y.z (ct.presIso F).symm f)

theorem isLocallyNoetherian (Z : ct.Mdl) : IsLocallyNoetherian Z.X :=
  have := GlobalTheory.ModelPresentation.isNoetherianRing_place Z.i.c ct.W ct.hp.ne_zero ct.hW
  have : IsProper (PSpace.str (Z.i.c.V ct.W) Z.n) := isProper_str _ _
  LocallyOfFiniteType.isLocallyNoetherian (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V ct.W) Z.n)

instance isFiniteQC_homMod_toMod (F₁ F₂ : ct.Sh Z) : IsFiniteQC (homMod F₁.toMod F₂.toMod) :=
  have := ct.isLocallyNoetherian Z
  isFiniteQC_homMod_cokernel (ct.isVB_free Z F₁.a' F₁.m') (ct.isVB_free Z F₁.a F₁.m) F₁.φ

def isoSymm {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) : ct.GIso F₂ F₁ := φ.symm

def homSh (F₁ F₂ : ct.Sh Z) : ct.Sh Z := Z.ofMod (homMod F₁.toMod F₂.toMod)

def homIso (F₁ F₂ : ct.Sh Z) : homMod F₁.toMod F₂.toMod ≅ (ct.homSh F₁ F₂).toMod := (ct.presIso _).symm

def isoSec {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) : ct.Sec (ct.homSh F₁ F₂) :=
  (ct.homIso F₁ F₂).hom.app _ (homOfRestrict φ.iso.hom)

theorem isVB_homSh {F₁ F₂ : ct.Sh Z} {r : ℕ} (h₁ : ct.IsInv F₁) (h₂ : IsVB F₂.toMod r) :
    IsVB (ct.homSh F₁ F₂).toMod r :=
  (isVB_homMod h₁ h₂).of_iso (ct.homIso F₁ F₂)

theorem homSh_inv (F₁ F₂ : ct.Sh Z) (h₁ : ct.IsInv F₁) (h₂ : ct.IsInv F₂) : ct.IsInv (ct.homSh F₁ F₂) :=
  ct.isVB_homSh h₁ h₂

theorem nrm_isoSec_eq {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y =
      sSup (nrmSet y.z (homMod F₁.toMod F₂.toMod) (compSec (𝟙 _) φ.iso.hom)) :=
  ct.nrm_ofMod _ _ y

theorem nrm_isoSec_pos_symm {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    0 < ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y ∧
      ct.nrm (ct.homSh F₂ F₁) (ct.isoSec (ct.isoSymm φ)) y =
        (ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y)⁻¹ := by
  rw [ct.nrm_isoSec_eq, ct.nrm_isoSec_eq]
  exact sSup_compSec_mul y.z ct.hp.ne_zero φ.isInv_left φ.isInv_right (𝟙 _) (𝟙 _)
    (IsVB.restrict φ.isInv_right _) φ.iso

def vrat {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) : ℝ :=
  -Real.logb p (ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y)

theorem nrm_isoSec {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y = (p : ℝ) ^ (-(ct.vrat φ y)) := by
  rw [vrat, neg_neg, Real.rpow_logb (Nat.cast_pos.2 ct.hp.pos) (by exact_mod_cast ct.hp.one_lt.ne')
    (ct.nrm_isoSec_pos_symm φ y).1]

theorem vrat_symm {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    ct.vrat (ct.isoSymm φ) y = -(ct.vrat φ y) := by
  rw [vrat, vrat, (ct.nrm_isoSec_pos_symm φ y).2, Real.logb_inv]

def oSh (Z : ct.Mdl) : ct.Sh Z := Z.ofMod (structureModule Z.X)

theorem oSh_inv (Z : ct.Mdl) : ct.IsInv (ct.oSh Z) :=
  (isVB_structureModule Z.X).of_iso (ct.presIso _).symm

def oOne (Z : ct.Mdl) : Γ((ct.oSh Z).toMod, ⊤) := (ct.presIso (structureModule Z.X)).inv.app ⊤ (oneSec ⊤)

theorem isFrame_oOne (Z : ct.Mdl) : VB.IsFrame fun _ : Fin 1 => ct.oOne Z :=
  (isFrame_one ⊤).map_iso (ct.presIso (structureModule Z.X)).inv

def secOf {F : ct.Sh Z} (φ : ct.GIso (ct.oSh Z) F) : ct.Sec F :=
  homApp (homOfRestrict φ.iso.hom) le_rfl (resM _ le_top (ct.oOne Z))

theorem nrm_secOf {F : ct.Sh Z} (φ : ct.GIso (ct.oSh Z) F) (y : ct.Pt Z) :
    ct.nrm F (ct.secOf φ) y = (p : ℝ) ^ (-(ct.vrat φ y)) := by
  rw [← nrm_isoSec, ct.nrm_isoSec_eq]
  exact sSup_compSec_eq y.z ct.hp.ne_zero (ct.oSh_inv Z) (𝟙 _) (ct.isFrame_oOne Z) φ.iso

structure SES (Z : ct.Mdl) : Type where

  F₁ : ct.Sh Z

  F₂ : ct.Sh Z

  F₃ : ct.Sh Z

  k₀ : ℕ

  f : modN F₁.toMod (p ^ k₀) ⟶ modN F₂.toMod (p ^ k₀)

  g : modN F₂.toMod (p ^ k₀) ⟶ modN F₃.toMod (p ^ k₀)

variable {ct}

def SES.ExactMod (s : ct.SES Z) (k : ℕ) : Prop :=
  ∃ (h : k ≤ s.k₀) (w : redMap (pow_dvd_pow p h) s.f ≫ redMap (pow_dvd_pow p h) s.g = 0),
    (ShortComplex.mk _ _ w).ShortExact

def SES.ofMaps {F₁ F₂ F₃ : ct.Sh Z} (f : F₁.toMod ⟶ F₂.toMod) (g : F₂.toMod ⟶ F₃.toMod) (k₀ : ℕ) : ct.SES Z :=
  ⟨F₁, F₂, F₃, k₀, modNMap f _, modNMap g _⟩

theorem SES.exactMod_ofMaps_iff {F₁ F₂ F₃ : ct.Sh Z} (f : F₁.toMod ⟶ F₂.toMod) (g : F₂.toMod ⟶ F₃.toMod) {k k₀ : ℕ}
    (h : k ≤ k₀) : (SES.ofMaps f g k₀).ExactMod k ↔
      ∃ w : modNMap f (p ^ k) ≫ modNMap g (p ^ k) = 0, (ShortComplex.mk _ _ w).ShortExact :=
  (exists_prop_of_true h).trans (exists_shortExact_congr (redMap_modNMap _ _) (redMap_modNMap _ _))

theorem SES.exactMod_of_splitting {F₁ F₂ F₃ : ct.Sh Z} {f : F₁.toMod ⟶ F₂.toMod} {g : F₂.toMod ⟶ F₃.toMod}
    {w : f ≫ g = 0} (σ : (ShortComplex.mk f g w).Splitting) {k k₀ : ℕ} (h : k ≤ k₀) :
    (SES.ofMaps f g k₀).ExactMod k := by
  rw [SES.exactMod_ofMaps_iff f g h]
  refine ⟨?_, ShortComplex.Splitting.shortExact
    { r := modNMap σ.r _, s := modNMap σ.s _, f_r := ?_, s_g := ?_, id := ?_ }⟩ <;>
    rw [← cancel_epi (cokernel.π _)]
  · simp [reassoc_of% w]
  · have := σ.f_r
    dsimp at this ⊢
    simp [reassoc_of% this]
  · have := σ.s_g
    dsimp at this ⊢
    simp [reassoc_of% this]
  · have := σ.id =≫ cokernel.π (p ^ k • 𝟙 F₂.toMod)
    dsimp at this ⊢
    simpa using this

end At

def shfTrue (ct : At S κ p) : ShfSt ct where
  vrat := ct.vrat
  SES := ct.SES
  ExactMod := At.SES.ExactMod
  homSh := ct.homSh
  homSh_inv := ct.homSh_inv
  isoSec := ct.isoSec
  nrm_isoSec := ct.nrm_isoSec
  isoSymm := ct.isoSymm
  vrat_symm := ct.vrat_symm
  oX := ct.oSh ct.Xm
  oX_inv := ct.oSh_inv _
  secOf := ct.secOf
  nrm_secOf := ct.nrm_secOf

end GlobalTheory.LocM
