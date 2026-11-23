module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.LevelActionGenerator

variable {X : Scheme.{0}}

private theorem pb_mul {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} (x y : T ⟶ A) :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  let e : Over.mk (T.hom ≫ 𝟙 X) ≅ T := Over.isoMk (Iso.refl _) (by simp)
  have he : e.hom.left = 𝟙 _ := rfl
  have key := h.2 T x y (e.hom ≫ x ≫ f) (e.hom ≫ y ≫ f)
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
    (by rw [Over.comp_left, Over.comp_left, he, Category.id_comp, hf])
  rw [← MonObj.comp_mul, Over.comp_left, he, Category.id_comp] at key
  apply Over.OverMorphism.ext
  rw [key, Over.comp_left, hf]

private theorem pb_one {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) (f : A ⟶ B) (hf : f.left = φ) {T : Over X} :
    (1 : T ⟶ A) ≫ f = 1 := by
  have h1 := pb_mul h f hf (1 : T ⟶ A) 1
  rw [_root_.mul_one] at h1
  simpa using h1

private theorem act_nat {O : Type} [Ring O] {A : Over X} [GrpObj A] [IsCommMonObj A] (act : OActN O A) {T : Over X}
    (u : T ⟶ A) (m : ℕ) : u ≫ act.act (m : O) = u ^ m := by
  induction m with
  | zero =>
    have h0 : act.act (0 : O) = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      simpa using this
    rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
  | succ m ih =>
    rw [Nat.cast_succ, act.add, act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

private theorem gen_mem {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) : (N : A) ∈ 𝔞 := by
  have h' : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)} := h
  have hm : (N : A) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 := by
    rw [h']
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (Ideal.mul_le_right (I := Ideal.span {a} ⊔ Ideal.span {(N : A)}) (J := 𝔞)) hm

end UpperTheory.LevelActionGenerator

open UpperTheory.LevelActionGenerator in
theorem UpperTheory.quotient_level_of_lattice_generation :
    LatGen → QLev := by
  intro hLat q _ D R R' _ _ _ b gb N N₀ c a 𝔞 hN hgen X s s₀ o o₀ n
  have hw : n.φ ≫ o₀.A.hom = o.A.hom := by simpa using n.cart.1.w
  haveI : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  let f : o.A ⟶ o₀.A := Over.homMk n.φ hw
  let g : o₀.A ⟶ o.A := Over.homMk (inv n.φ) (by rw [IsIso.inv_comp_eq, hw])
  have hfl : f.left = n.φ := rfl
  have hfg : f ≫ g = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hgf : g ≫ f = 𝟙 _ := by
    apply Over.OverMorphism.ext
    simp [f, g]
  have hinj : ∀ {T : Over X} (u v : T ⟶ o.A), u ≫ f = v ≫ f → u = v := by
    intro T u v huv
    have := congrArg (· ≫ g) huv
    simpa [Category.assoc, hfg] using this
  have hmul : ∀ {T : Over X} (u v : T ⟶ o.A), (u * v) ≫ f = (u ≫ f) * (v ≫ f) :=
    fun u v => pb_mul n.cart f hfl u v
  have hone : ∀ {T : Over X}, (1 : T ⟶ o.A) ≫ f = 1 := pb_one n.cart f hfl
  have hone' : ∀ {T : Over X}, (1 : T ⟶ o₀.A) ≫ g = 1 := by
    intro T
    apply hinj
    rw [Category.assoc, hgf, Category.comp_id, hone]
  have hact : ∀ c' : D.O, o.act.act c' ≫ f = f ≫ o₀.act.act c' := by
    intro c'
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    exact n.act c'
  have e_add : ∀ u v : D.La, o.eta (u + v) = o.eta u * o.eta v := fun u v => o.eta_add u v
  have e_lin : ∀ (c' : D.O) (u : D.La), o.eta (c' • u) = o.eta u ≫ o.act.act c' :=
    fun c' u => o.eta_lin c' u
  have e_ker : ∀ u : D.La, o.eta (N • u) = 1 := fun u => o.eta_ker u
  obtain ⟨hL1, hL2⟩ := hLat q D a N 𝔞 hN hgen
  refine ⟨fun y => o.eta (algebraMap (𝓞 D.F) D.O a • y) ≫ f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y z
    simp only
    rw [smul_add, e_add, hmul]
  · intro c' y
    simp only
    have hcomm : algebraMap (𝓞 D.F) D.O a • (c' • y) = c' • (algebraMap (𝓞 D.F) D.O a • y) := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    rw [hcomm, e_lin, Category.assoc, hact, Category.assoc]
  · intro y hy
    obtain ⟨z, hz⟩ := (hL1 y).2 hy
    simp only
    rw [hz, e_ker, hone]
  · intro k _ _ x
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o.geom k x _ hβ
    have hI' : ∀ y : D.La, toUnit (Over.mk x) ≫ o.eta y = I.ev N y := fun y => hI y
    have I_add : ∀ u v : D.La, I.ev N (u + v) = I.ev N u * I.ev N v := fun u v => I.add N u v
    have I_lin : ∀ (c' : D.O) (u : D.La), I.ev N (c' • u) = I.ev N u ≫ o.act.act c' :=
      fun c' u => I.lin N c' u
    have I_ker : ∀ u : D.La, I.ev N u = 1 ↔ ∃ v : D.La, u = N • v := fun u => I.ker N hN u
    have I_onto : ∀ r : Over.mk x ⟶ o.A, r ^ N = 1 ↔ ∃ u : D.La, I.ev N u = r :=
      fun r => I.onto N hN r
    constructor
    · intro y hy
      simp only at hy
      rw [← Category.assoc, ← hone] at hy
      have h1 := hinj _ _ hy
      rw [hI'] at h1
      obtain ⟨z, hz⟩ := (I_ker _).1 h1
      exact (hL1 y).1 ⟨z, hz⟩
    · intro g₀ hg₀
      have hg'act : ∀ c' : D.O, (g₀ ≫ g) ≫ o.act.act c' = (g₀ ≫ o₀.act.act c') ≫ g := by
        intro c'
        apply hinj
        simp only [Category.assoc, hact, reassoc_of% hgf, hgf, Category.comp_id]
      have hkill : ∀ c' ∈ 𝔞, (g₀ ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c') = 1 := by
        intro c' hc'
        rw [hg'act, hg₀ c' (by rwa [pow_one]), hone']
      have hpow : (g₀ ≫ g) ^ N = 1 := by
        have hn := act_nat o.act (g₀ ≫ g) N
        have hc : ((N : ℕ) : D.toG.O) = algebraMap (𝓞 D.F) D.O (N : 𝓞 D.F) := (map_natCast _ N).symm
        rw [hc] at hn
        rw [← hn]
        exact hkill _ (gen_mem hgen)
      obtain ⟨x', hx'⟩ := (I_onto (g₀ ≫ g)).1 hpow
      have hcond : ∀ c' ∈ 𝔞, ∃ z : D.La, algebraMap (𝓞 D.F) D.O c' • x' = N • z := by
        intro c' hc'
        apply (I_ker _).1
        rw [I_lin, hx']
        exact hkill c' hc'
      obtain ⟨y, z, hyz⟩ := hL2 x' hcond
      refine ⟨y, ?_⟩
      have hyI : toUnit (Over.mk x) ≫ o.eta (algebraMap (𝓞 D.F) D.O a • y) = g₀ ≫ g := by
        rw [hI', ← hx', hyz, I_add, (I_ker (N • z)).2 ⟨z, rfl⟩, _root_.mul_one]
      simp only
      rw [← Category.assoc, hyI, Category.assoc, hgf, Category.comp_id]
  · intro y
    rfl
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo.QCompPf

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {b : Base D R} {gb : GBase D.toG R'} {N N₀ c : ℕ} {X X' X₁ X₂ : Scheme.{0}} {s : X ⟶ Sp R'}
  {s' : X' ⟶ Sp R'} {s₁ : X₁ ⟶ Sp R} {s₂ : X₂ ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'}
  {u₁ : Obj b N₀ s₁} {u₂ : Obj b N₀ s₂} {f : X ⟶ X₁} {g : X₁ ⟶ X₂} {e : X' ⟶ X}

private def after (n : QMap o u₁ f c) (m : ObjMap u₁ u₂ g) : QMap o u₂ (f ≫ g) c where
  φ := n.φ ≫ m.φ
  φ₂ := n.φ₂ ≫ m.φ₂
  cart := n.cart.comp m.cart
  sq := MapComp.isSquare_comp n.sq m.sq
  act x := by
    have h₁ := n.act x
    have h₂ := m.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (n.pol).trans o.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
    (MapComp.lbIso_pull_comp m.pol n.φ₂ rfl)
  eta y := by
    have h₁ := n.eta y
    have h₂ := m.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private def before (m : GObjMap o' o e) (n : QMap o u₁ f c) : QMap o' u₁ (e ≫ f) c where
  φ := m.φ ≫ n.φ
  φ₂ := m.φ₂ ≫ n.φ₂
  cart := m.cart.comp n.cart
  sq := MapComp.isSquare_comp m.sq n.sq
  act x := by
    have h₁ := m.act x
    have h₂ := n.act x
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]
  pol := (m.pol).trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u₁.isLB _)
    (MapComp.lbIso_pull_comp n.pol m.φ₂ rfl)
  eta y := by
    have h₁ := m.eta (c • y)
    have h₂ := n.eta y
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, h₂]

private theorem factor (n' : QMap o u₂ (f ≫ g) c) (m : ObjMap u₁ u₂ g) :
    ∃ n : QMap o u₁ f c, n'.φ = n.φ ≫ m.φ := by
  have hw : n'.φ ≫ u₂.A.hom = (o.A.hom ≫ f) ≫ g := by
    rw [n'.cart.1.w, Category.assoc]
  let ℓ : o.A.left ⟶ u₁.A.left := m.cart.1.lift n'.φ (o.A.hom ≫ f) hw
  have hℓφ : ℓ ≫ m.φ = n'.φ := m.cart.1.lift_fst _ _ _
  have hℓs : ℓ ≫ u₁.A.hom = o.A.hom ≫ f := m.cart.1.lift_snd _ _ _
  obtain ⟨ℓ₂, hsq⟩ := MapComp.exists_isSquare (G := u₁.A) (G' := o.A) hℓs
  have hsq₂ : ℓ₂ ≫ m.φ₂ = n'.φ₂ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hsq m.sq)
    rw [hℓφ]
    exact n'.sq
  refine ⟨⟨ℓ, ℓ₂, ?_, hsq, ?_, ?_, ?_⟩, hℓφ.symm⟩
  · exact IsGrpPullback.cancel m.cart (IsGrpPullback.congr n'.cart rfl hℓφ.symm) hℓs
  · intro x
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, m.act x, ← Category.assoc, hℓφ]
      exact n'.act x
    · rw [Category.assoc, Category.assoc, hℓs, Over.w, hℓs, ← Category.assoc, Over.w]
  · exact LBIso.trans o.isLB (pull_isLB u₂.isLB _) (pull_isLB u₁.isLB _) n'.pol
      (MapComp.lbIso_pull_comp m.pol ℓ₂ hsq₂.symm).symm
  · intro y
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hℓφ, n'.eta y, m.eta y, Category.assoc]
    · rw [Category.assoc, Category.assoc, hℓs, ← Category.assoc, Over.w]
      simp [Over.w]

private theorem bridge [IsIso f] (n : QMap o u₁ f c) (n' : QMap o u₂ (f ≫ g) c) :
    ∃ m : ObjMap u₁ u₂ g, n'.φ = n.φ ≫ m.φ := by
  haveI hiso : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  have hinvw : inv n.φ ≫ o.A.hom = u₁.A.hom ≫ inv f := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, n.cart.1.w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hinv : IsGrpPullback u₁.A o.A (inv f) (inv n.φ) :=
    IsGrpPullback.cancel n.cart
      (IsGrpPullback.congr (GlobalTheory.EndLoc.isGrpPullback_id u₁.A) (by simp) (by simp)) hinvw
  have hcart : IsGrpPullback u₁.A u₂.A g (inv n.φ ≫ n'.φ) :=
    IsGrpPullback.congr (IsGrpPullback.comp hinv n'.cart) (by simp) rfl
  obtain ⟨ψ₂, hψ⟩ := MapComp.exists_isSquare (G := o.A) (G' := u₁.A) hinvw
  have hid : Geo.Tor.IsSquare (𝟙 u₁.A.left) (𝟙 (u₁.A ⊗ u₁.A).left) := by
    constructor <;> simp
  have hψn : ψ₂ ≫ n.φ₂ = 𝟙 _ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp hψ n.sq)
    rw [IsIso.inv_hom_id]
    exact hid
  refine ⟨⟨inv n.φ ≫ n'.φ, ψ₂ ≫ n'.φ₂, hcart, MapComp.isSquare_comp hψ n'.sq, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    have hx : Over.Hom.left (u₁.act.act x) ≫ inv n.φ = inv n.φ ≫ Over.Hom.left (o.act.act x) := by
      rw [IsIso.comp_inv_eq, Category.assoc, n.act x, IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, hx, Category.assoc, n'.act x, Category.assoc]
  · exact LBIso.trans u₁.isLB (pull_isLB u₁.isLB _) (pull_isLB u₂.isLB _)
      (GlobalTheory.SiegLower.lbIso_pull_id u₁.isLB)
      (LBIso.trans (pull_isLB u₁.isLB _) (pull_isLB o.isLB _) (pull_isLB u₂.isLB _)
        (MapComp.lbIso_pull_comp n.pol ψ₂ hψn.symm).symm
        (MapComp.lbIso_pull_comp n'.pol ψ₂ rfl))
  · intro y
    have hy : Over.Hom.left (u₁.eta y) = inv f ≫ Over.Hom.left (o.eta (c • y)) ≫ n.φ := by
      rw [n.eta y, IsIso.inv_hom_id_assoc]
    rw [hy]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, n'.eta y, IsIso.inv_hom_id_assoc]
  · simp

end UpperTheory.Gal.Int.Geo.QCompPf

open UpperTheory.Gal.Int.Geo.QCompPf in
theorem UpperTheory.quotient_map_comp : QComp := by
  intro q _ D R R' _ _ _ b gb N N₀ c X X₁ X₂ s s₁ s₂ o u₁ u₂ f g
  refine ⟨fun n m => ⟨after n m, rfl⟩, fun n' m => factor n' m, fun hf n n' => bridge n n', ?_⟩
  intro X' s' o' e m n
  exact ⟨before m n, rfl⟩
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientSeparatedOfTraceUnitCrt
section
open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem UpperTheory.quotient_separated_of_trace_unit_crt :
    GPull → QComp → QIso → QUniq → TrEta → TrEtaPt → TrUnit → CongCRT → BaseSep := by
  intro hGP hQC hQI hQU hTE hTP hTU hCRT
  intro p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C u hu W Ω _ _ z hz
  have huN : L.CongOne S.N₀ u ∧ L.CongOne S.N₀ u⁻¹ := hu
  have hu1 : u ∈ L.KN 1 := KN_anti (one_dvd _) hu
  have hInt : Integ L u := integ_of_mem hu1
  rw [hLev]
  refine ⟨hu1, ?_⟩
  rw [S.lev]
  obtain ⟨hcrt1, hcrt2⟩ := hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hInt
  rw [hcrt1]
  refine ⟨huN.1, ?_⟩
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  rw [hcrt2 a N hNpos N.2.2 hNum.2]
  intro y
  set x := (algebraMap (𝓞 D.F) D.O a) • y with hx
  refine (hTP p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans Ω z x).2 rfl x ?_
  have ht : (toUnit (Over.mk z)).left = z := by
    simpa using Over.w (toUnit (Over.mk z))
  obtain ⟨oz, ⟨mz⟩⟩ := hGP _ _ gb (N : ℕ) (T.M N).X (Sp Ω) (T.M N).s z (T.M N).univ
  obtain ⟨nW, hnW⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans hu1
  have heta : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ W.ψ = W.o.eta (c • y') := by
    intro y'
    refine hTE p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans S.N₀ c c hNum.1 hNum.1
      y' y' ?_
    exact huN.1 _ (inAf_mem D y')
  obtain ⟨nI, hnI⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb N N S.N₀ c c _ _ _ _ (T.M N).univ W.o S.Y.univ _ W.ψ hiso W.trans.1
    W.trans.2.1 hlb heta nW
  obtain ⟨nA, hnA⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ oz z mz C.m
  obtain ⟨nB, hnB⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ (W.π ≫ C.j) (𝟙 _)).2.2.2
    _ _ oz z mz nI
  have hfeq : z ≫ W.π ≫ C.j = z ≫ C.j := hz
  have hAB : mz.φ ≫ Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = mz.φ ≫ C.m.φ := by
    generalize hF : z ≫ W.π ≫ C.j = F at nB hnB
    have hF' : F = z ≫ C.j := hF.symm.trans hfeq
    subst hF'
    have h := hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c S.std.three S.std.cop _ _ _ _ _ _ _ nB nA
    rw [hnB, hnI, hnW, hnA] at h
    exact h
  apply Over.OverMorphism.ext
  apply nW.cart.1.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [hnW, reassoc_of% (W.φ.eta x)]
    have hl := C.lv y
    have hr : Over.Hom.left ((T.M N).univ.eta x) ≫ C.m.φ = C.j ≫ Over.Hom.left (S.Y.lv y) := hl
    have hz' := mz.eta x
    rw [ht]
    rw [← reassoc_of% hz', hAB, reassoc_of% hz', hr, reassoc_of% hfeq]
  · simp only [Over.comp_left, Category.assoc, Over.w]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RationalSplittingExists
section
open UpperTheory.Gal.Int.Geo

private theorem matrix_unique_algEquiv (R A m : Type) [CommSemiring R] [Semiring A] [Algebra R A]
    [fm : Fintype m] [dm : DecidableEq m] [Unique m] : Nonempty (Matrix m m A ≃ₐ[R] A) := by
  refine ⟨{ toFun := fun M => M default default
            invFun := fun a => Matrix.of fun _ _ => a
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_
            map_add' := ?_
            commutes' := ?_ }⟩
  · intro M
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  · intro a
    simp
  · intro M N
    simp [Matrix.mul_apply]
  · intro M N
    simp
  · intro r
    simp [Matrix.algebraMap_matrix_apply]

open scoped TensorProduct in
theorem UpperTheory.rational_splitting_exists :
    SplitQ := by
  intro p _ D hm q _
  haveI : Unique (Fin D.m) :=
    { default := ⟨0, by omega⟩
      uniq := fun i => Fin.ext (by have := i.2; simp; omega) }
  let e0 : D.O ≃ₐ[NumberField.RingOfIntegers D.F] NumberField.RingOfIntegers D.F :=
    (AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨D.algebraMap_injective hm, GlobalTheory.T.integers_surjective_of_rank_one p D hm⟩).symm
  exact ⟨(Algebra.TensorProduct.congr e0 AlgEquiv.refl).trans
    (matrix_unique_algEquiv _ _ _).some.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SiteExistsOfSplittingAndPowerProjector
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.site_exists_of_splitting_and_power_projector :
    MIn → SplitQ → BaseEx → PowProj → SiteEx := by
  intro hM hS hB hP
  intro p _ D G hSc E _ _ e gb hstd w q _ r 𝔴 𝔫 hpl hat hlev
  have sp := hS p D hSc.m1 q
  obtain ⟨N₀, 𝔞, h3, hcq, hcp, hsup, hupow, hlv⟩ := hlev
  obtain ⟨f, b, hmat, hstdb, hqmem, hnorm⟩ :=
    hB q (datAt hat sp) hSc.a1 hSc.m1 E e gb hstd w 𝔴 r hpl hat.le N₀ h3 hcq
  obtain ⟨M⟩ := hM.ex q (datAt hat sp) (Ow w) b N₀ h3 hcq
  have hEt : UpperTheory.Gal.FiniteEtaleModels.IsEtIdeal b 𝔞 :=
    (hM.placeOf q (datAt hat sp) (Ow w) b r 𝔴 hat.max hstdb.pmem hSc.a1 hstdb.ule hstdb.tw 𝔞 hsup).2 hupow
  obtain ⟨Y, π, ρ, hov, ⟨hmπ⟩, hgal⟩ := hM.finModel q (datAt hat sp) (Ow w) b N₀ h3 hcq 𝔞 1 hEt M
  have hfin : IsFinite π := hgal.fin
  have het : Etale π := hgal.etale
  have hMproj : IsProjOver M.s := hM.proj q (datAt hat sp) (Ow w) b N₀ h3 hcq hSc.cpt M
  have hYproj : IsProjOver Y.s := by
    rw [← hov]
    exact _root_.GlobalTheory.isProjOver_comp_of_finite (Ow w) M.X Y.X π M.s hfin hMproj
  have hYsm : SmoothOfRelativeDimension (0 + (datAt hat sp).a * ((datAt hat sp).n - 1)) Y.s := by
    rw [← hov]
    haveI : SmoothOfRelativeDimension 0 π := by
      rw [← AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero]
      exact het
    haveI := M.smooth
    infer_instance
  have hPw := fun k => hP q (datAt hat sp) (Ow w) b N₀ h3 hcq Y.X Y.s Y.univ k
  exact ⟨⟨hat, sp, f, b, hmat, N₀, 𝔞, hstdb, hqmem, hnorm, hcp, hsup, hupow, hlv, M, Y, π, hov, hmπ,
    hfin, het, fun k => (hPw k).1 hYproj, fun k => (hPw k).2 _ hYsm⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.StandardDatumExists
section
open UpperTheory.Gal.Int.Geo

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen in
theorem UpperTheory.standard_datum_exists :
    StdEx := by
  intro p _ D ha E _ _ e
  let φ : 𝓞 D.F →+* E := (e : D.F →+* E).comp (algebraMap (𝓞 D.F) D.F)
  have key : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]
    ring
  have hroot : φ D.ω ^ 2 - (D.tr : E) * φ D.ω + (D.nm : E) = 0 := by
    simpa using congrArg φ key
  have hsub : Subsingleton (Fin D.toG.a) := by
    have h : D.toG.a = 1 := ha
    rw [h]
    infer_instance
  exact ⟨{ ρ := φ D.ω
           ρ_root := hroot
           t := fun _ => φ
           t_ω := fun _ => rfl
           comax := fun i j hij => (hij (Subsingleton.elim i j)).elim }, rfl, fun _ _ => rfl⟩
end

