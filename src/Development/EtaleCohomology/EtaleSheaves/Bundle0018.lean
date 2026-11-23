module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.MayerVietorisSequence

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1),
  (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ),
    (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧
    (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧
    ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧
  ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V')
    (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c,
    pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c)

def OpenCov : Prop := ∀ (R : Type) [CommRing R] {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
  [IsOpenImmersion g], Set.range f ∪ Set.range g = Set.univ → Cover2 R (sch.map f) (sch.map g)

def SchPB : Prop := ∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X), IsIso (pullbackComparison sch f g)

variable (R : Type) [CommRing R]

theorem pull_hom_inv {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) (x : H R E F n) :
    pull R e F n (pull R (inv e) F n x) = x := by
  rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem pull_inv_hom {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R (inv e) F n (pull R e F n x) = x := by
  rw [← pull_comp, IsIso.inv_hom_id, pull_id]

theorem pull_inj_of_iso' {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := fun x y h => by
  rw [← pull_inv_hom R e F n x, h, pull_inv_hom]

theorem comp_sq (hP : SchPB) {U V X U' V' X' : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) (f' : U' ⟶ X') (g' : V' ⟶ X')
    (u : U ⟶ U') (v : V ⟶ V') (p : X ⟶ X') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g')
    (hu' : sch.map f ≫ sch.map p = sch.map u ≫ sch.map f') (hv' : sch.map g ≫ sch.map p = sch.map v ≫ sch.map g') :
    have := hP f g; have := hP f' g'
    inv (pullbackComparison sch f g) ≫ sch.map (pullback.map f g f' g' u v p hu hv) =
      pullback.map _ _ _ _ (sch.map u) (sch.map v) (sch.map p) hu' hv' ≫ inv (pullbackComparison sch f' g') := set_option synthInstance.maxHeartbeats 200000 in by
  have := hP f g; have := hP f' g'
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackComparison_comp_fst, pullback.lift_fst, ← Functor.map_comp, pullback.lift_fst_assoc]
    rw [pullbackComparison_comp_fst_assoc, ← Functor.map_comp]
  · simp only [Category.assoc, pullbackComparison_comp_snd, pullback.lift_snd, ← Functor.map_comp, pullback.lift_snd_assoc]
    rw [pullbackComparison_comp_snd_assoc, ← Functor.map_comp]

end LateralTheory.E.MayerVietorisSequence

open LateralTheory.E.MayerVietorisSequence in
theorem LateralTheory.E.t_E2Cut.MV_of_three (hS : MVSpc) (hC : OpenCov) (hP : SchPB) : LateralTheory.E.t_E2Cut.MV := by
  classical
  intro hyp R _ F
  obtain ⟨d, hex, hnat⟩ := hS hyp.a1 R F
  refine ⟨fun {U V X} f g n => if h : Cover2 R (sch.map f) (sch.map g) then
    have := hP f g; (d _ _ h n).comp (pull R (inv (pullbackComparison sch f g)) F n) else 0, ?_, ?_⟩
  · intro U V X f g _ _ hcov n
    have := hP f g
    have h := hC R f g hcov
    obtain ⟨h1, h2, h3⟩ := hex (sch.map f) (sch.map g) h n
    have hf : sch.map (pullback.fst f g) = pullbackComparison sch f g ≫ pullback.fst _ _ :=
      (pullbackComparison_comp_fst _ _ _).symm
    have hg : sch.map (pullback.snd f g) = pullbackComparison sch f g ≫ pullback.snd _ _ :=
      (pullbackComparison_comp_snd _ _ _).symm
    simp only [dif_pos h, AddMonoidHom.comp_apply]
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      rw [hf, hg, pull_comp, pull_comp] at hab
      exact (h1 a b).1 (pull_inj_of_iso' R _ F n hab)
    · intro w
      rw [h2]
      constructor
      · rintro ⟨a, b, hab⟩
        refine ⟨a, b, ?_⟩
        rw [hf, hg, pull_comp, pull_comp, ← map_sub, ← hab, pull_hom_inv]
      · rintro ⟨a, b, rfl⟩
        refine ⟨a, b, ?_⟩
        rw [hf, hg, pull_comp, pull_comp, ← map_sub, pull_inv_hom]
    · intro x
      rw [h3]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨pull R (pullbackComparison sch f g) F n c, by rw [pull_inv_hom]⟩
      · rintro ⟨w, rfl⟩
        exact ⟨_, rfl⟩
  · intro U V X U' V' X' f g f' g' _ _ _ _ hcov hcov' u v p hu hv n w
    have := hP f g; have := hP f' g'
    have h := hC R f g hcov
    have h' := hC R f' g' hcov'
    simp only [dif_pos h, dif_pos h', AddMonoidHom.comp_apply]
    have hu' : sch.map f ≫ sch.map p = sch.map u ≫ sch.map f' := by rw [← Functor.map_comp, hu, Functor.map_comp]
    have hv' : sch.map g ≫ sch.map p = sch.map v ≫ sch.map g' := by rw [← Functor.map_comp, hv, Functor.map_comp]
    rw [hnat (sch.map f) (sch.map g) (sch.map f') (sch.map g') (sch.map p) (sch.map u) (sch.map v) hu' hv' h h' n,
      ← pull_comp, ← pull_comp, comp_sq hP f g f' g' u v p hu hv hu' hv']

namespace LateralTheory.E.MayerVietorisSequence

theorem schPB : SchPB := fun f g => by
  have : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance
  infer_instance

end LateralTheory.E.MayerVietorisSequence

namespace LateralTheory.E.MayerVietorisSequence

def SES : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w,
  (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact

def LES : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {N K L M : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M)
    (e : L ⟶ M) (w : biprod.lift a (-b) ≫ biprod.desc c e = 0), (ShortComplex.mk _ _ w).ShortExact →
    ∀ n : ℤ, HK R N F n →+ HK R M F (n + 1),
  (∀ {N K L M : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M) (e : L ⟶ M) (w : biprod.lift a (-b) ≫ biprod.desc c e = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) (n : ℤ),
    (∀ x y, HK.pull R a F n x = HK.pull R b F n y ↔ ∃ z, HK.pull R c F n z = x ∧ HK.pull R e F n z = y) ∧
    (∀ t, d a b c e w hS n t = 0 ↔ ∃ x y, t = HK.pull R a F n x - HK.pull R b F n y) ∧
    ∀ z, (HK.pull R c F (n + 1) z = 0 ∧ HK.pull R e F (n + 1) z = 0) ↔ ∃ t, d a b c e w hS n t = z) ∧
  ∀ {N K L M N' K' L' M' : Cx R} (a : N ⟶ K) (b : N ⟶ L) (c : K ⟶ M) (e : L ⟶ M) (a' : N' ⟶ K') (b' : N' ⟶ L')
    (c' : K' ⟶ M') (e' : L' ⟶ M') (w : biprod.lift a (-b) ≫ biprod.desc c e = 0)
    (w' : biprod.lift a' (-b') ≫ biprod.desc c' e' = 0) (hS : (ShortComplex.mk _ _ w).ShortExact)
    (hS' : (ShortComplex.mk _ _ w').ShortExact) (φN : N ⟶ N') (φK : K ⟶ K') (φL : L ⟶ L') (φM : M ⟶ M'),
    a ≫ φK = φN ≫ a' → b ≫ φL = φN ≫ b' → c ≫ φM = φK ≫ c' → e ≫ φM = φL ≫ e' → ∀ (n : ℤ) t,
    HK.pull R φM F (n + 1) (d a' b' c' e' w' hS' n t) = d a b c e w hS n (HK.pull R φN F n t)

theorem mvSpc_of (hE : SES) (hL : LES) : MVSpc := by
  intro _ R _ F
  obtain ⟨d, hex, hnat⟩ := hL R F
  refine ⟨fun f g h n => d _ _ _ _ (hE R f g h).choose (hE R f g h).choose_spec n, ?_, ?_⟩
  · intro U V E f g h n
    exact hex _ _ _ _ (hE R f g h).choose (hE R f g h).choose_spec n
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    refine hnat _ _ _ _ _ _ _ _ _ _ _ _ ((chains R).map (pullback.map f g f' g' u v p hu hv)) ((chains R).map u)
      ((chains R).map v) ((chains R).map p) ?_ ?_ ?_ ?_ n c
    · rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
    · rw [← Functor.map_comp, ← Functor.map_comp, pullback.lift_snd]
    · rw [← Functor.map_comp, ← Functor.map_comp, hu]
    · rw [← Functor.map_comp, ← Functor.map_comp, hv]

end LateralTheory.E.MayerVietorisSequence
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PiecesPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.PiecesPf

lemma sq1 {T S C' C : Type} [CommRing T] [CommRing S] [CommRing C'] [CommRing C]
    (a : T →+* C') (π : T →+* S) (ρ : C' →+* C) (b : S →+* C) (hρ : Function.Surjective ρ) (hπ : Function.Surjective π)
    (hcomm : ρ.comp a = b.comp π) (hker : RingHom.ker ρ = (RingHom.ker π).map a) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom π) (CommRingCat.ofHom ρ) (CommRingCat.ofHom b) := by
  have w : CommRingCat.ofHom a ≫ CommRingCat.ofHom ρ = CommRingCat.ofHom π ≫ CommRingCat.ofHom b := by
    ext x; exact congrArg (fun f : T →+* C => f x) hcomm
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w ?_ ?_ ?_ ?_)
  · intro s
    refine CommRingCat.ofHom (ρ.liftOfSurjective hρ ⟨s.inl.hom, ?_⟩)
    rw [hker, Ideal.map_le_iff_le_comap]
    intro t ht
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    simp only [Ideal.mem_comap, RingHom.mem_ker] at ht ⊢
    rw [h1, ht, map_zero]
  · intro s
    ext x
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    exact RingHom.liftOfSurjective_comp_apply ρ hρ _ x
  · intro s
    ext x
    obtain ⟨t, rfl⟩ := hπ x
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 ⊢
    rw [← RingHom.comp_apply b π, ← hcomm, RingHom.comp_apply, RingHom.liftOfSurjective_comp_apply]
    exact h1
  · intro s m hm _
    ext x
    obtain ⟨y, rfl⟩ := hρ x
    simp only [CommRingCat.hom_ofHom]
    rw [RingHom.liftOfSurjective_comp_apply]
    have := congrArg (fun f => f.hom y) hm
    simpa using this

theorem Pieces_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) :
    LateralTheory.E.FinEtSectionPf.Pieces := by
  intro _ _ S C _ _ _ _ hQA
  obtain ⟨T, _, _, π, hAIC, hπ⟩ := hQA
  obtain ⟨C', _, _, ρ, hEt, hρ, hcomm, hker⟩ := hL T S C π hπ
  have := hEt
  obtain ⟨n, e', he', hoi⟩ := hA T C' hAIC
  refine ⟨n, ρ ∘ e', he'.map ρ, fun j => ?_⟩
  let fₘ : Localization.Away (e' j) →+* Localization.Away (ρ (e' j)) :=
    IsLocalization.Away.map _ _ ρ (e' j)
  have : IsLocalization ((Submonoid.powers (e' j)).map ρ) (Localization.Away (ρ (e' j))) := by
    rw [Submonoid.map_powers]; infer_instance
  have H : fₘ.comp (algebraMap C' _) = (algebraMap C _).comp ρ := IsLocalization.map_comp _
  have sq2 := CommRingCat.isPushout_of_isLocalization ρ fₘ H (Submonoid.powers (e' j))
  have sq := (sq1 (algebraMap T C') π ρ (algebraMap S C) hρ hπ hcomm hker).paste_horiz sq2.flip
  have pb := isPullback_SpecMap_of_isPushout _ _ _ _ sq
  have hj := hoi j
  rw [CommRingCat.ofHom_comp] at hj
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) pb hj
  rw [CommRingCat.ofHom_comp]
  exact this

end LateralTheory.E.PiecesPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.QuotAcycCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.QuotAcycCut

def ProdAcyc : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] (n : ℕ) (R : Fin n → Type) [∀ k, CommRing (R k)],
  Nonempty (A ≃+* ∀ k, R k) → (∀ k, Acyc q (sp (R k))) → Acyc q (sp A)

def Hens : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    IsUnit (q : c.pt) ∧ ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

theorem goal_of (hP : ProdAcyc) (hH : Hens) : LateralTheory.E.t_E2Cut.QuotAcyc := by
  intro H q B _ _ I hB hq
  obtain ⟨J, _, _, D, c, hc, hD, hqc, K, hK, ⟨e⟩⟩ := hH q B I hB hq

  have hst : ∀ j, Acyc q (sp (D.obj j)) := by
    intro j
    obtain ⟨m, R, _, hR, hiso⟩ := hD j
    refine hP H q (D.obj j) m R hiso fun k => ?_
    have := (hR k).1
    exact H.b5 q (R k) (hR k).2.1 (hR k).2.2

  have hC : Acyc q (sp c.pt) := by
    intro n i hn
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ x : Ht q (sp c.pt) n i, x = 0 := by
      intro x
      obtain ⟨j, y, rfl⟩ := (H.b1 q D c hc n i).1 x hqc
      have := hst j n i hn
      rw [Subsingleton.elim y 0, map_zero]
    rw [h0 x, h0 y]

  have hCK : Acyc q (sp (c.pt ⧸ K)) := by
    intro n i hn
    have := hC n i hn
    have hE := H.e1 q c.pt K hqc i n
    exact hE.2.subsingleton
  exact hP H q (B ⧸ I) 1 (fun _ => c.pt ⧸ K) ⟨e.trans (RingEquiv.piUnique (fun _ : Fin 1 => c.pt ⧸ K)).symm⟩ fun _ => hCK

end LateralTheory.E.QuotAcycCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SHEqvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHEqvPf
open LateralTheory.E.t_E3Cut

def SecBij : Prop := SHSection → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) →
  SH A → SH B → Function.Bijective (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s)

def SecPre : Prop := SHSection → ∀ (q : ℕ) (i : ℤ) (A : CommRingCat.{0}), SH A →
  Function.Bijective (ofRings.sec (twF q i) (Spec A))

def TwFBij : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B →
  Function.Bijective ((twF q i).map (Spec.map f).appTop).hom

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (j : V ⟶ U)
    (m : M.obj Γ(U, ⊤)) : Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op
  have h2 := congrArg (fun φ => φ.hom m) h
  exact h2.symm

theorem SecBij_of (hP : SecPre) (hT : TwFBij) : SecBij := by
  intro hSec q _ i A B f hq hA hB
  have key : (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s) =
      ofRings.sec (twF q i) (Spec B) ∘ ((twF q i).map (Spec.map f).appTop).hom ∘
        (Equiv.ofBijective _ (hP hSec q i A hA)).symm := by
    funext s
    obtain ⟨m, rfl⟩ := (hP hSec q i A hA).2 s
    simp only [Function.comp]
    rw [Equiv.ofBijective_symm_apply_apply]
    exact sec_res _ _ _
  rw [key]
  exact (hP hSec q i B hB).comp ((hT q i f hq hA hB).comp (Equiv.bijective (Equiv.ofBijective _ (hP hSec q i A hA)).symm))

theorem bij_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (g : M →+ N) : Function.Bijective g :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

theorem SHEqv_of_secBij (hSec : SHSection) (hB : SecBij) : SHEqv := by
  intro hyp q _ i A B f hq hA hBs n
  obtain ⟨_, _, _, _, _, hA9, _, hB2, _⟩ := hyp
  obtain ⟨hneg, e, he, -⟩ := hA9 (ZMod q) (tw q i)
  rcases lt_trichotomy n 0 with h | h | h
  · haveI := hneg (sch.obj (Spec A)) n h
    haveI := hneg (sch.obj (Spec B)) n h
    exact bij_of_subsingleton _
  · subst h
    have key : ⇑(pull (ZMod q) (sch.map (Spec.map f)) (tw q i) 0) =
        (e (Spec B)) ∘ (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s) ∘ (e (Spec A)).symm := by
      funext x
      simp only [Function.comp]
      rw [← he]
      simp
    show Function.Bijective (pull (ZMod q) (sch.map (Spec.map f)) (tw q i) 0)
    rw [key]
    exact (e _).bijective.comp ((hB hSec q i f hq hA hBs).comp (e _).symm.bijective)
  · haveI := hB2 (ZMod q) A hA (tw q i) n h
    haveI := hB2 (ZMod q) B hBs (tw q i) n h
    exact bij_of_subsingleton _

end LateralTheory.E.SHEqvPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SHExistsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SHExistsPf

def SHLoc : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ IsLocalHom f.hom

def LocAt : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A) [r.IsPrime],
  IE (CommRingCat.ofHom (algebraMap A (Localization.AtPrime r)))

def Comp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

theorem SHExists_of (hL : SHLoc) (hA : LocAt) (hC : Comp) : t_E3Cut.SHExists := by
  intro A r hr
  let L : CommRingCat.{0} := CommRingCat.of (Localization.AtPrime r)
  let g : A ⟶ L := CommRingCat.ofHom (algebraMap A (Localization.AtPrime r))
  haveI : IsLocalRing L := inferInstanceAs (IsLocalRing (Localization.AtPrime r))
  obtain ⟨O, h, hIE, hSH, hloc⟩ := hL L
  refine ⟨O, g ≫ h, hC g h (hA A r) hIE, hSH, fun a => ?_⟩
  have key : IsUnit (algebraMap A (Localization.AtPrime r) a) ↔ a ∈ r.primeCompl :=
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime r) r a
  have e : (g ≫ h).hom a = h.hom (algebraMap A (Localization.AtPrime r) a) := rfl
  rw [e]
  constructor
  · intro ha hu
    have := (key.1 (isUnit_of_map_unit h.hom _ hu))
    exact this ha
  · intro hn
    by_contra ha
    exact hn ((key.2 ha).map h.hom)

end LateralTheory.E.SHExistsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SHTensorPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHTensorPf

def LocTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → IsLocalRing Z

def SepTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → ∀ (_ : IsLocalRing Z),
  IsSepClosed (IsLocalRing.ResidueField Z)

theorem intPush {A X B Z : CommRingCat.{0}} {x : A ⟶ X} {b : A ⟶ B} {u : X ⟶ Z} {v : B ⟶ Z}
    (hp : IsPushout x b u v) (hb : b.hom.IsIntegral) : u.hom.IsIntegral := by
  have h : (RingHom.toMorphismProperty fun f => f.IsIntegral).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.isIntegral_isStableUnderBaseChange
  exact h.of_isPushout hp hb

theorem idem_local (R : Type) [CommRing R] [IsLocalRing R] (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right; exact (sub_eq_zero.mp ((h.mul_right_eq_zero).mp h0)).symm
  · left; exact (h.mul_left_eq_zero).mp h0

theorem SHTensor_of (hH : LateralTheory.E.t_E3Cut.HensInt) (hL : LocTensor) (hS : SepTensor) : LateralTheory.E.t_E3Cut.SHTensor := by
  intro A X B Z x b u v hp hA hX hx hb hB
  have hZ : IsLocalRing Z := hL x b u v hp hA hX hx hb hB
  have hsep := hS x b u v hp hA hX hx hb hB hZ
  obtain ⟨hXh, _⟩ := hX
  obtain ⟨hZh⟩ := hH X Z u.hom (intPush hp hb) (idem_local Z)
  exact ⟨hZh, hsep⟩

end LateralTheory.E.SHTensorPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpSOfIntegralInjective
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ULAPf
open LateralTheory.E.t_E3Cut

theorem spS_of_integral_injective {C D : CommRingCat.{0}} (g : C ⟶ D) (hi : g.hom.IsIntegral)
    (hj : Function.Injective g.hom) : SpS g := by
  intro r hr
  letI := g.hom.toAlgebra
  have : Algebra.IsIntegral C D := ⟨hi⟩
  have hk : RingHom.ker (algebraMap C D) ≤ r := by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C D)).1 hj]; exact bot_le
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral r ⊥ (by rw [Ideal.under_def C (B := D), ← RingHom.ker_eq_comap_bot (algebraMap C D)]; exact hk)
  exact ⟨Q, hQ, hQc⟩

theorem SpS.comp {C D E : CommRingCat.{0}} {f : C ⟶ D} {g : D ⟶ E} (hf : SpS f) (hg : SpS g) : SpS (f ≫ g) := by
  intro r hr
  obtain ⟨Q0, hQ0, hQ0c⟩ := hf r hr
  obtain ⟨Q, hQ, hQc⟩ := hg Q0 hQ0
  exact ⟨Q, hQ, by rw [CommRingCat.hom_comp, ← Ideal.comap_comap, hQc, hQ0c]⟩

theorem ULA_of (hS : Stalk) (hP : AlgResProps) (hE : AICExt) (hD : DomCover) (hL : LocIE) (hU : ULAStalk) : ULA := by
  intro H q _ i A X h hq hA hX hIE hloc C c hc
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
  refine hS H q i (pC A ≫ h) hq (fun _ c => AlgRes c) ?_ ?_ ?_ C c hc
  · intro C D E Z c f g u v hpo _ hf hg
    have hv : AlgRes v := p3 f g u v hpo (p2 c f hf)
    have := p1 (c ≫ g) v hg hv
    rw [hpo.w, ← Category.assoc]; exact this
  · intro C D c f hc hf
    exact p1 c f hc (p4 f hf)
  · intro C c hc
    obtain ⟨D0, g0, hg0i, hg0j, hg0a⟩ := hE C
    obtain ⟨D, g1, hg1i, hg1s, hg1d⟩ := hD D0 hg0a
    have hgi : (g0 ≫ g1).hom.IsIntegral := by
      rw [CommRingCat.hom_comp]; exact RingHom.IsIntegral.trans _ _ hg0i hg1i
    refine ⟨D, g0 ≫ g1, hgi, SpS.comp (spS_of_integral_injective g0 hg0i hg0j) hg1s,
      p1 c (g0 ≫ g1) hc (p5 _ hgi), ?_⟩
    intro r hr
    have := hr
    obtain ⟨hdom, haic⟩ := hg1d r
    let o : D ⟶ CommRingCat.of (Localization.AtPrime r) := CommRingCat.ofHom (algebraMap D _)
    have ho : AlgRes o := p6 D (Localization.AtPrime r) r.primeCompl
    refine ⟨CommRingCat.of (Localization.AtPrime r), o, IsLocalRing.maximalIdeal _,
      hL D (Localization.AtPrime r) r.primeCompl, inferInstance,
      IsLocalization.AtPrime.under_maximalIdeal _ r, ?_⟩
    haveI : IsDomain (CommRingCat.of (Localization.AtPrime r)) := hdom
    haveI : IsLocalRing (CommRingCat.of (Localization.AtPrime r)) :=
      inferInstanceAs (IsLocalRing (Localization.AtPrime r))
    exact hU H q i h hq hA hX hIE hloc _ (c ≫ (g0 ≫ g1) ≫ o) haic
      (p1 c _ hc (p1 _ o (p5 _ hgi) ho))

end LateralTheory.E.ULAPf

end
end

