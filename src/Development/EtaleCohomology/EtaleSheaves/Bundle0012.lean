module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0008
public import Development.EtaleCohomology.EtaleSheaves.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCMapPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCMapPf

def TwNat : Prop := ∀ (q : ℕ) (i : ℤ) (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
  Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)

def LCSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (Y : Type)
  (φ : LocallyConstant (PrimeSpectrum B) Y) (a b : Sec F (Spec (CommRingCat.of B))),
  (∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : Y), (∀ v : V, φ (g.base v) = c) → Sec.res g a = Sec.res g b) → a = b

def LCGlue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (Y : Type)
  (φ : LocallyConstant (PrimeSpectrum B) Y) (s : Y → Sec F (Spec (CommRingCat.of B))),
  ∃ t : Sec F (Spec (CommRingCat.of B)), ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : Y),
    (∀ v : V, φ (g.base v) = c) → Sec.res g t = Sec.res g (s c)

theorem twNat : TwNat := by
  intro q i V U g ζ
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op
  have h2 := congrArg (fun k => k.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))) h
  simp only [ModuleCat.hom_comp] at h2
  simp only [LinearMap.coe_comp] at h2
  unfold twGen ofRings.sec
  refine h2.symm.trans (congrArg ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom ?_)
  simp only [twF, Functor.comp_map]
  rw [ModuleCat.hom_ofHom]
  first
  | (erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; done)
  | (erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  | exact congrArg (Submodule.Quotient.mk (p := twRel q i _)) (Finsupp.mapDomain_single (f := Prim.map g.appTop.hom) (a := ζ) (b := (1 : ULift (ZMod q))))

theorem nsmul_val {q : ℕ} [NeZero q] (i : ℤ) (U : Scheme.{0}) (x : Sec (tw q i) U) (c : ZMod q) :
    c.val • x = (ULift.up c : ULift (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift (ZMod q))]
  congr 1
  ext
  exact (ULift.down_natCast _).trans (ZMod.natCast_zmod_val c)

def sG {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B) (c : ZMod q) : Sec (tw q i) (Spec (CommRingCat.of B)) :=
  (ULift.up c : ULift (ZMod q)) • twGen i (gam ζ)

theorem res_smul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift R) (x : Sec F U) :
    Sec.res g (r • x) = r • Sec.res g x := by
  simp [Sec.res]

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := by
  simp [Sec.res]

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

def tG (hG : LCGlue) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)) :
    Sec (tw q i) (Spec (CommRingCat.of B)) :=
  Classical.choose (hG (ZMod q) (tw q i) B (ZMod q) φ (sG i ζ))

theorem tG_spec (hG : LCGlue) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B)
    (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)) (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : ZMod q)
    (h : ∀ v : V, φ (g.base v) = c) : Sec.res g (tG hG i ζ φ) = Sec.res g (sG i ζ c) :=
  Classical.choose_spec (hG (ZMod q) (tw q i) B (ZMod q) φ (sG i ζ)) V g c h

theorem tG_add (hG : LCGlue) (hS : LCSep) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B)
    (φ ψ : LocallyConstant (PrimeSpectrum B) (ZMod q)) : tG hG i ζ (φ + ψ) = tG hG i ζ φ + tG hG i ζ ψ := by
  let χ : LocallyConstant (PrimeSpectrum B) (ZMod q × ZMod q) :=
    ⟨fun x => (φ x, ψ x), IsLocallyConstant.comp₂ φ.2 ψ.2 Prod.mk⟩
  refine hS (ZMod q) (tw q i) B _ χ _ _ ?_
  intro V g c hc
  have h1 : ∀ v : V, φ (g.base v) = c.1 := fun v => congrArg Prod.fst (hc v)
  have h2 : ∀ v : V, ψ (g.base v) = c.2 := fun v => congrArg Prod.snd (hc v)
  have h3 : ∀ v : V, (φ + ψ) (g.base v) = c.1 + c.2 := fun v => by
    show φ (g.base v) + ψ (g.base v) = _
    rw [h1, h2]
  rw [tG_spec hG i ζ _ V g _ h3, res_add, tG_spec hG i ζ _ V g _ h1, tG_spec hG i ζ _ V g _ h2, ← res_add]
  congr 1
  unfold sG
  rw [← add_smul]
  rfl

theorem LCMap_of_parts (hT : TwNat) (hS : LCSep) (hG : LCGlue) : LCMap := by
  intro q _ i
  refine ⟨fun B _ ζ => AddMonoidHom.mk' (tG hG i ζ) (tG_add hG hS i ζ), ?_, ?_⟩
  · intro B C _ _ f ζ φ
    change Sec.res _ (tG hG i ζ φ) = tG hG i (ζ.map f) (lcMap f φ)
    refine hS (ZMod q) (tw q i) C _ (lcMap f φ) _ _ ?_
    intro V g c hc
    have hc' : ∀ v : V, φ ((g ≫ Spec.map (CommRingCat.ofHom f)).base v) = c := fun v => by
      exact hc v
    rw [← res_comp, tG_spec hG i ζ φ V _ c hc', tG_spec hG i (ζ.map f) _ V g c hc]
    unfold sG
    rw [res_smul, res_smul, hT, hT]
    have hP : Prim.map (g ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom (gam ζ) = Prim.map g.appTop.hom (gam (ζ.map f)) := by
      apply Subtype.ext
      change (g ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ζ.1) =
        g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (f ζ.1))
      have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      congr 1
      rw [← CommRingCat.comp_apply, ← hn]
      rfl
    rw [hP]
  · intro B _ ζ c
    change tG hG i ζ _ = _
    have h := tG_spec hG i ζ (LocallyConstant.const _ c) _ (𝟙 _) c (fun v => rfl)
    rw [res_id, res_id] at h
    rw [h, nsmul_val]
    rfl

def fibS (B : Type) [CommRing B] {Y : Type} (φ : LocallyConstant (PrimeSpectrum B) Y) : Sieve (Spec (CommRingCat.of B)) where
  arrows V g := ∃ c, ∀ v : V, φ (g.base v) = c
  downward_closed := by
    rintro V W g ⟨c, hc⟩ k
    exact ⟨c, fun w => hc (k.base w)⟩

theorem fibS_mem (B : Type) [CommRing B] {Y : Type} (φ : LocallyConstant (PrimeSpectrum B) Y) :
    fibS B φ ∈ Scheme.etaleTopology (Spec (CommRingCat.of B)) := by
  refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).mpr ?_
  let O : PrimeSpectrum B → (Spec (CommRingCat.of B)).Opens := fun x =>
    ⟨φ ⁻¹' {φ x}, φ.isLocallyConstant.isOpen_fiber _⟩
  refine ⟨Scheme.Cover.mkOfCovers (PrimeSpectrum B) (fun x => (O x).toScheme) (fun x => (O x).ι)
    (fun x => ⟨x, ⟨x, rfl⟩, by simp⟩), ?_⟩
  rintro _ _ ⟨x⟩
  refine ⟨φ x, fun v => ?_⟩
  have hv := v.2
  first
  | exact hv
  | (simp only [Scheme.Cover.mkOfCovers_f, Scheme.Opens.ι_apply]; exact hv)
  | (simp [O, Scheme.Cover.mkOfCovers_f] at hv ⊢; exact hv)

theorem isSheafT {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property

theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (Z : Scheme.{0}) [IsEmpty Z] (a b : Sec F Z) : a = b :=
  ((isSheafT F) _ (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext (fun _ _ h => h.elim)

theorem lcSep : LCSep := by
  intro R _ F B _ Y φ a b h
  exact ((isSheafT F) _ (fibS_mem B φ)).isSeparatedFor.ext (fun V g hg => h V g hg.choose hg.choose_spec)

theorem lcGlue : LCGlue := by
  intro R _ F B _ Y φ s
  let x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (fibS B φ).arrows :=
    fun V g hg => Sec.res g (s hg.choose)
  have key : ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c d : Y), (∀ v : V, φ (g.base v) = c) →
      (∀ v : V, φ (g.base v) = d) → Sec.res g (s c) = Sec.res g (s d) := by
    intro V g c d hc hd
    by_cases hV : Nonempty V
    · obtain ⟨v⟩ := hV
      rw [← hc v, ← hd v]
    · have : IsEmpty V := not_nonempty_iff.1 hV
      exact sec_empty F V _ _
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    change Sec.res (k ≫ g) (s _) = Sec.res k (Sec.res g (s _))
    rw [← res_comp]
    exact key W (k ≫ g) _ _ ((fibS B φ).downward_closed hg k).choose_spec (fun w => hg.choose_spec (k.base w))
  obtain ⟨t, ht, -⟩ := (isSheafT F) _ (fibS_mem B φ) x hx
  refine ⟨t, fun V g c hc => ?_⟩
  have h1 := ht g ⟨c, hc⟩
  refine h1.trans (key V g _ _ (Exists.choose_spec (p := fun c => ∀ v : V, φ (g.base v) = c) ⟨c, hc⟩) hc)

theorem LCMap_of : LCMap := LCMap_of_parts twNat lcSep lcGlue

end LateralTheory.E.LCMapPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LFactorPf
section
noncomputable section
open Polynomial

namespace LateralTheory.E.LFactorPf

def LEtaleLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ ψ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp ψ = φ

theorem LFactor_of (hE : LEtaleLift) : LateralTheory.E.HensIdemCut.LFactor := by
  intro A _ I _ f g₀ h₀ hf hg hh hgh e
  rcases subsingleton_or_nontrivial (A ⧸ I) with hs | hs
  · have hI : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    have h1 : (1 : A) ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson_bot]
      exact HenselianRing.jac (I := I) (hI ▸ Submodule.mem_top)
    have hu := Ideal.mem_jacobson_bot.mp h1 (-1)
    have hA : Subsingleton A := by
      simp at hu
      exact subsingleton_of_zero_eq_one (by simpa using hu)
    refine ⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hn : f.natDegree = g₀.natDegree + h₀.natDegree := by
    rw [← hg.natDegree_mul hh, ← e, hf.natDegree_map]
  let p : MonicDegreeEq A f.natDegree := .mk f hf rfl
  have e' : g₀ * h₀ = p.1.map (algebraMap A (A ⧸ I)) := e.symm
  let φ := (UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I) _ _ hn p).symm
    ⟨(.mk g₀ hg rfl, .mk h₀ hh rfl), e', hgh⟩
  obtain ⟨ψ, hψ⟩ := hE A I _ φ
  let q := UniversalCoprimeFactorizationRing.homEquiv A _ _ hn p ψ
  refine ⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, ?_, ?_, ?_⟩
  · have := q.2.1
    simpa [p] using this.symm
  · have := UniversalCoprimeFactorizationRing.homEquiv_comp_fst A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)
    rw [hψ, Equiv.apply_symm_apply] at this
    exact congr($(this).1).symm
  · have := UniversalCoprimeFactorizationRing.homEquiv_comp_snd A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)
    rw [hψ, Equiv.apply_symm_apply] at this
    exact congr($(this).1).symm

end LateralTheory.E.LFactorPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LIdemPf
section
noncomputable section
open Polynomial

namespace LateralTheory.E.LIdemPf

theorem LIdem_of : LateralTheory.E.HensIdemCut.LIdem := by
  intro A _ I B _ φ hJ b hb N g h hg hh hgh
  set J := I.map φ with hJdef
  let π := Ideal.Quotient.mk J
  let ψ : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
  have hcomp : ψ.comp (Ideal.Quotient.mk I) = π.comp φ := by
    ext a; simp [ψ, π, Ideal.quotientMap_mk]
  have key : ∀ p : A[X], π (p.eval₂ φ b) = (p.map (Ideal.Quotient.mk I)).eval₂ ψ (π b) := by
    intro p
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
  set G := g.eval₂ φ b with hGdef
  set H := h.eval₂ φ b with hHdef
  set e := π b with hedef
  have hG : π G = e ^ N := by rw [key, hg]; simp
  have hH : π H = (e - 1) ^ N := by rw [key, hh]; simp [eval₂_pow, eval₂_sub, eval₂_X, eval₂_one]
  have he : e * e = e := by
    have : π (b * b - b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [map_sub, map_mul] at this
    exact sub_eq_zero.mp this
  have hcop : IsCoprime (e ^ N) ((e - 1) ^ N) :=
    (show IsCoprime e (e - 1) from ⟨1, -1, by ring⟩).pow
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨v', rfl⟩ := Ideal.Quotient.mk_surjective v
  set s := u' * G + v' * H with hsdef
  have hs : π s = π 1 := by
    simp only [hsdef, map_add (f := _), map_mul, hG, hH, map_one]
    exact huv
  have hsJ : s - 1 ∈ Ideal.jacobson (⊥ : Ideal B) := hJ (Ideal.Quotient.eq.mp hs)
  have hunit : IsUnit s := by
    have := (Ideal.mem_jacobson_bot.mp hsJ) 1
    simpa using this
  obtain ⟨w, hw⟩ := hunit
  have hsum : (↑w⁻¹ * u') * G + (↑w⁻¹ * v') * H = 1 := by
    have : (↑w⁻¹ : B) * s = 1 := by rw [← hw]; exact Units.inv_mul w
    rw [hsdef] at this
    linear_combination this
  refine ⟨(↑w⁻¹ * u') * G, ?_, ?_⟩
  · show (↑w⁻¹ * u') * G * ((↑w⁻¹ * u') * G) = (↑w⁻¹ * u') * G
    linear_combination ((↑w⁻¹ * u') * G) * hsum - (↑w⁻¹ * u') * (↑w⁻¹ * v') * hgh
  · rw [← Ideal.Quotient.eq]
    change π ((↑w⁻¹ * u') * G) = e
    have hsum' := congrArg π hsum
    simp only [map_add (f := _), map_mul, map_one, hG, hH] at hsum' ⊢
    set α := π ↑w⁻¹ * π u'
    set γ := π ↑w⁻¹ * π v'
    cases N with
    | zero =>
      have h0 : (1 : B ⧸ J) = 0 := by
        have := congrArg π hgh
        simpa [map_mul, hG, hH] using this
      have := subsingleton_of_zero_eq_one h0.symm
      exact Subsingleton.elim _ _
    | succ n =>
      have hp : e ^ (n + 1) = e := IsIdempotentElem.pow_succ_eq n he
      have h1 : e * (e - 1) ^ (n + 1) = 0 := by
        calc e * (e - 1) ^ (n + 1) = (e * e - e) * (e - 1) ^ n := by ring
          _ = 0 := by rw [he, sub_self, zero_mul]
      rw [hp] at hsum' ⊢
      linear_combination e * hsum' - α * he - γ * h1

end LateralTheory.E.LIdemPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LJacPf
section
namespace LateralTheory.E.LJacPf

theorem LJac_of : LateralTheory.E.HensIdemCut.LJac := by
  intro A _ I hH B _ φ hφ
  letI := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  have hI : I ≤ Ideal.jacobson ⊥ := by simpa only [Ideal.jacobson_bot] using hH.jac
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro m ⟨-, hm⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (m.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φ hφ m
  refine hI.trans ?_
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, this⟩

end LateralTheory.E.LJacPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LMonicPf
section
noncomputable section
open Polynomial

namespace LateralTheory.E.LMonicPf

theorem map_mk_eq_X_pow {A : Type} [CommRing A] (I : Ideal A) (p : A[X]) (hp : p.Monic)
    (h : ∀ i ≠ p.natDegree, p.coeff i ∈ I) :
    p.map (Ideal.Quotient.mk I) = X ^ p.natDegree := by
  ext i
  rw [coeff_map, coeff_X_pow]
  split_ifs with hi
  · subst hi; rw [hp.coeff_natDegree, map_one]
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i hi)

theorem LMonic_of : LateralTheory.E.HensIdemCut.LMonic := by
  intro A _ I B _ φ hφ b hb
  cases subsingleton_or_nontrivial A
  · have : Subsingleton B := by
      refine ⟨fun x y => ?_⟩
      rw [← mul_one x, ← mul_one y, ← map_one φ, Subsingleton.elim (1 : A) 0, map_zero,
        mul_zero, mul_zero]
    exact ⟨0, 1, monic_one, Subsingleton.elim _ _, by simp⟩
  let := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  obtain ⟨p, hpm, hp0, hpI⟩ :=
    exists_monic_aeval_eq_zero_forall_mem_of_mem_map (R := A) (S := B) (I := I) (x := b * b - b) hb
  have hqe : ((X : A[X]) * X - X) = X ^ 2 - X := by rw [sq]
  have hq : ((X : A[X]) * X - X).Monic := by
    rw [hqe]
    exact monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))
  have hqd : ((X : A[X]) * X - X).natDegree ≠ 0 := by
    intro h
    have h1 := congrArg (eval 0) ((Polynomial.Monic.natDegree_eq_zero hq).mp h)
    simp at h1
  refine ⟨p.natDegree, p.comp (X * X - X), hpm.comp hq hqd, ?_, ?_⟩
  · rw [eval₂_comp]
    simp only [eval₂_mul, eval₂_sub, eval₂_X]
    rw [aeval_def] at hp0
    exact hp0
  · rw [Polynomial.map_comp, map_mk_eq_X_pow I p hpm hpI, X_pow_comp, ← mul_pow]
    congr 1
    simp [C_1]
    ring
end LateralTheory.E.LMonicPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCompPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def LeafCoprod : Prop := Hyps → ∀ (q : ℕ) (n i : ℤ) (m : ℕ) (Z : Fin m → Scheme.{0}),
  (∀ j, Finite (Ht q (sch.obj (Z j)) n i)) → Finite (Ht q (sch.obj (∐ Z)) n i)

def LeafCompGeom : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p],
  ∃ (m : ℕ) (Z : Fin m → Scheme.{0}) (ι : ∀ j, Z j ⟶ X), (∀ j, IsClosedImmersion (ι j) ∧ IsIntegral (Z j)) ∧
    IsProper (Sigma.desc ι) ∧ Surjective (Sigma.desc ι)

theorem LeafComp_of (hC : LeafCoprod) (hG : LeafCompGeom) : LeafComp := by
  intro hH q k _ X p _ n i hZ
  obtain ⟨m, Z, ι, hι, hP, hS⟩ := hG k p
  exact ⟨∐ Z, Sigma.desc ι, hP, hS, hC hH q n i m Z (fun j => hZ (Z j) (ι j) (hι j).1 (hι j).2)⟩

end LateralTheory.E.E4
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCover2Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafCover2Pf

variable (R : Type) [CommRing R]

theorem pre_eq {P Q : PSh} (G : Shv R) (φ : Q ⟶ P) (u v : (free R).obj P ⟶ G)
    (h : (free R).map φ ≫ u = (free R).map φ ≫ v) :
    (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ u.hom) =
      (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ v.hom) := by
  have k := congrArg (fun w => toSheafify Scheme.etaleTopology ((freeP R).obj Q) ≫ w.hom) h
  exact (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) u.hom).trans
    (k.trans (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) v.hom).symm)

theorem gen_eq {P Q : PSh} (G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : Q ⟶ P) (a b : (freeP R).obj P ⟶ G)
    (h : (freeP R).map φ ≫ a = (freeP R).map φ ≫ b) (Y : Scheme.{0}) (y : Q.obj (op Y)) :
    a.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) := by
  have e : ((freeP R).map φ).app (op Y) (ModuleCat.freeMk (ULift.up y)) =
      ModuleCat.freeMk (ULift.up (φ.app _ y)) := by
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have h3 := congrArg (fun w => w (ModuleCat.freeMk (ULift.up y)))
    (congrArg (fun t => ConcreteCategory.hom t) (NatTrans.congr_app h (op Y)))
  simp only [NatTrans.comp_app] at h3
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, e] at h3
  exact h3

theorem loc_eq {P : PSh} (G : Shv R) (a b : (freeP R).obj P ⟶ G.obj) (X : Scheme.{0}) (x : P.obj (op X))
    (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X)
    (h : ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
      a.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x)))) :
    a.app (op X) (ModuleCat.freeMk (ULift.up x)) = b.app (op X) (ModuleCat.freeMk (ULift.up x)) := by
  have key : ∀ (c : (freeP R).obj P ⟶ G.obj) (Y : Scheme.{0}) (k : Y ⟶ X),
      G.obj.map k.op (c.app (op X) (ModuleCat.freeMk (ULift.up x))) = c.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) := by
    intro c Y k
    have n1 := ConcreteCategory.congr_hom (c.naturality k.op) (ModuleCat.freeMk (ULift.up x))
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at n1
    rw [← n1]
    congr 1
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have hE := Presheaf.IsSheaf.hom_ext G.2 ⟨S, hS⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (a.app (op X) (ModuleCat.freeMk (ULift.up x)))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (b.app (op X) (ModuleCat.freeMk (ULift.up x))))) (by
      intro I
      ext1
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, one_smul]
      erw [key a, key b]
      exact h _ _ I.hf)
  have := ConcreteCategory.congr_hom hE (1 : ULift R)
  simpa using this

theorem LeafCover2_of : LateralTheory.E.D2.LeafCover2 := by
  intro R _ U V E f g hf hg hc
  refine ⟨hf, hg, fun n => ⟨fun {G} u v huv => ?_⟩⟩
  induction n using Opposite.rec with | op n => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = SimplexCategory.mk m := ⟨n.len, rfl⟩
  have h1 : (free R).map (f.app _) ≫ u = (free R).map (f.app _) ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have h2 : (free R).map (g.app _) ≫ u = (free R).map (g.app _) ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  have p1 := pre_eq R G _ u v h1
  have p2 := pre_eq R G _ u v h2
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (P := (freeP R).obj (E.obj (op (SimplexCategory.mk m)))) _ _ _ G.2 ?_
  apply NatTrans.ext
  funext Y
  induction Y using Opposite.rec with | op X => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  obtain ⟨S, hS, hk⟩ := hc m X x
  refine loc_eq R G _ _ X x S hS ?_
  intro Y k hk'
  rcases hk Y k hk' with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy]; exact gen_eq R _ _ _ _ p1 Y y
  · rw [← hy]; exact gen_eq R _ _ _ _ p2 Y y

end LateralTheory.E.LeafCover2Pf
end
end

