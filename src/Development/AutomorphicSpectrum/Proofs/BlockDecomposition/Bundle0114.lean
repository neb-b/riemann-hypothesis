module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocSplit
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LocSplitProof

theorem locSplit : CrystallineSemistableComparison.E.LocSplit := by
  intro U hU P hP
  obtain ⟨S, hS, hSP⟩ := hP
  rw [Scheme.etaleTopology, Scheme.mem_grothendieckTopology_iff] at hS
  obtain ⟨𝒰, h𝒰⟩ := hS
  have hsurj : Surjective (Limits.Sigma.desc 𝒰.f) := by
    constructor
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    refine ⟨(Limits.Sigma.ι 𝒰.X i) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc, hy]
  have het : Etale (Limits.Sigma.desc 𝒰.f) := by
    have := 𝒰.sigma.map_prop ⟨⟩
    simpa [Scheme.Cover.sigma_f] using this
  obtain ⟨s, hs⟩ := hU _ (Limits.Sigma.desc 𝒰.f) het hsurj
  have hlc : IsLocallyConstant (fun u : U => ((sigmaMk 𝒰.X).symm (s u)).1) := by
    intro t
    have hfst : IsOpen (Sigma.fst ⁻¹' t : Set (Σ i, 𝒰.X i)) := by
      rw [isOpen_sigma_iff]
      intro i
      by_cases hi : i ∈ t
      · convert isOpen_univ
        ext
        simp [hi]
      · convert isOpen_empty
        ext
        simp [hi]
    exact hfst.preimage ((sigmaMk 𝒰.X).symm.continuous.comp s.continuous)
  refine ⟨𝒰.I₀, ⟨fun u => ((sigmaMk 𝒰.X).symm (s u)).1, hlc⟩, ?_⟩
  intro V g a hg
  have hrange : Set.range (g ≫ s) ⊆ Set.range (Limits.Sigma.ι 𝒰.X a) := by
    rintro _ ⟨v, rfl⟩
    have h1 : ((sigmaMk 𝒰.X).symm (s (g v))).1 = a := hg v
    rcases hq : (sigmaMk 𝒰.X).symm (s (g v)) with ⟨i, y⟩
    rw [hq] at h1
    subst h1
    refine ⟨y, ?_⟩
    have h2 : sigmaMk 𝒰.X ⟨i, y⟩ = s (g v) := by rw [← hq]; simp
    rw [sigmaMk_mk] at h2
    rw [h2, Scheme.Hom.comp_apply]
  obtain ⟨l, hl⟩ : ∃ l, l ≫ Limits.Sigma.ι 𝒰.X a = g ≫ s :=
    ⟨_, IsOpenImmersion.lift_fac (Limits.Sigma.ι 𝒰.X a) (g ≫ s) hrange⟩
  have hgl : g = l ≫ 𝒰.f a := by
    have h3 : l ≫ 𝒰.f a = l ≫ Limits.Sigma.ι 𝒰.X a ≫ Limits.Sigma.desc 𝒰.f := by simp
    rw [h3, ← Category.assoc, hl, Category.assoc, hs, Category.comp_id]
  rw [hgl]
  exact hSP V _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk a)) l)

end GlobalTheory.CompanionTheory.LocSplitProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapNsmulTwGen
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CstE.KapRedP

theorem up_smul_eq {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (r : ZMod q) (c : ℕ)
    (h : (c : ZMod q) = r) (m : M) : (ULift.up r : ULift.{1} (ZMod q)) • m = c • m := by
  have e : (ULift.up r : ULift.{1} (ZMod q)) = ((c : ℕ) : ULift.{1} (ZMod q)) := by
    ext; rw [ULift.down_natCast, h]
  rw [e, Nat.cast_smul_eq_nsmul]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := congrArg (fun ψ => ψ.hom x) (φ.hom.naturality g.op)
  exact h.symm

theorem map_nsmul_twGen {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (c : ℕ) :
    Sec.map (resι _ (tw q i)) (c • twGen i ζ) = c • resGen i ζ :=
  map_nsmul _ _ _

theorem kapRed : CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.KapRed := by
  intro hLc _ hKap hRed Q q _ _ h i U ζ ξ hξ f
  obtain ⟨W, j, hj, -, -, hG⟩ := hLc U (ZMod Q) f
  refine (hG (ZMod q) ((GlobalTheory.EtC.res _ (tw q i)).X 0)
    (fun a => Sec.res (j a) (Sec.map (resι _ _) (kap i ξ (f.map (ZMod.castHom h (ZMod q))))))).unique
    (fun a => ?_) (fun a => rfl)
  have hξ' : (primRes (j a) ξ).1 = (primRes (j a) ζ).1 ^ (Q / q) := by
    change (j a).appTop.hom ξ.1 = ((j a).appTop.hom ζ.1) ^ (Q / q)
    rw [hξ, map_pow]
  have hL : Sec.res (j a) (kap i ζ f) = a.val • twGen i (primRes (j a) ζ) := by
    rw [(hKap Q i U ζ f).1 (W a) (j a) a (hj a)]
    exact up_smul_eq a a.val (ZMod.natCast_zmod_val a) _
  have hR : Sec.res (j a) (kap i ξ (f.map (ZMod.castHom h (ZMod q)))) = a.val • twGen i (primRes (j a) ξ) := by
    rw [(hKap q i U ξ (f.map (ZMod.castHom h (ZMod q)))).1 (W a) (j a) (ZMod.castHom h (ZMod q) a)
      (fun v => by simp [hj a v])]
    exact up_smul_eq _ a.val (by rw [ZMod.castHom_apply, ZMod.natCast_val]) _
  rw [(redMap Q q i).nat (j a) 0, res_map, res_map, hL, hR, map_nsmul_twGen, map_nsmul_twGen, map_nsmul,
    hRed Q q h i (W a) (primRes (j a) ζ) (primRes (j a) ξ) hξ']

end GlobalTheory.CompanionTheory.CstE.KapRedP
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBasicOpenOfIsUnitSub
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.RootPowLC

theorem mem_basicOpen_prod {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤)) (u : U)
    (h : ∀ a ∈ t, u ∈ U.basicOpen (s a)) : u ∈ U.basicOpen (∏ a ∈ t, s a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, U.basicOpen_of_isUnit isUnit_one]
    trivial
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    exact ⟨h a (Finset.mem_insert_self a t), ih fun b hb => h b (Finset.mem_insert_of_mem hb)⟩

theorem exists_notMem_basicOpen {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤))
    (h : ∏ a ∈ t, s a = 0) (u : U) : ∃ a ∈ t, u ∉ U.basicOpen (s a) := by
  by_contra hc
  push_neg at hc
  have hm := mem_basicOpen_prod t s u hc
  rw [h, Scheme.basicOpen_zero] at hm
  exact hm

theorem mem_basicOpen_of_isUnit_sub {U : Scheme.{0}} (x y : Γ(U, ⊤)) (h : IsUnit (x - y)) (u : U)
    (hx : u ∉ U.basicOpen x) : u ∈ U.basicOpen y := by
  rw [Scheme.mem_basicOpen_top] at hx ⊢
  have h1 : IsUnit (U.presheaf.germ ⊤ u trivial (x - y)) := h.map _
  rw [map_sub, sub_eq_add_neg] at h1
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h2 | h2
  · exact absurd h2 hx
  · simpa using h2.neg

theorem isUnit_appTop_of_mem {V U : Scheme.{0}} (g : V ⟶ U) (x : Γ(U, ⊤))
    (h : ∀ v : V, g v ∈ U.basicOpen x) : IsUnit (g.appTop.hom x) := by
  refine RingedSpace.isUnit_of_isUnit_germ V.toRingedSpace ⊤ _ fun v _ => ?_
  have e : V.basicOpen (g.appTop.hom x) = g ⁻¹ᵁ U.basicOpen x := (Scheme.preimage_basicOpen g x).symm
  have hv : v ∈ V.basicOpen (g.appTop.hom x) := by
    rw [e]
    exact h v
  exact (Scheme.mem_basicOpen_top V (g.appTop.hom x) v).1 hv

theorem exists_isPow (hP : PrimAlg) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤))
    (r : Γ(U, ⊤)) (hr : r ^ q = 1) :
    ∃ f : LocallyConstant U (ZMod q), IsPow ζ f r ∧
      ∀ (u : U) (a : ZMod q), u ∉ U.basicOpen (r - ζ.1 ^ a.val) → f u = a := by
  classical
  have hprod : ∏ a : ZMod q, (r - ζ.1 ^ a.val) = 0 := by
    rw [← (hP q _ ζ).2.2.1 r, hr, sub_self]
  have hex : ∀ u : U, ∃ a : ZMod q, u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ (fun a : ZMod q => r - ζ.1 ^ a.val) hprod u
    exact ⟨a, ha⟩
  have huniq : ∀ (u : U) (a b : ZMod q), a ≠ b → u ∉ U.basicOpen (r - ζ.1 ^ a.val) →
      u ∈ U.basicOpen (r - ζ.1 ^ b.val) := by
    intro u a b hab ha
    apply mem_basicOpen_of_isUnit_sub _ _ _ u ha
    have hd : (r - ζ.1 ^ a.val) - (r - ζ.1 ^ b.val) = ζ.1 ^ b.val - ζ.1 ^ a.val := by ring
    rw [hd]
    exact (hP q _ ζ).2.1 b a (Ne.symm hab)
  obtain ⟨f0, hf0def⟩ : ∃ f0 : U → ZMod q, f0 = fun u => Classical.choose (hex u) := ⟨_, rfl⟩
  have hf0 : ∀ u, u ∉ U.basicOpen (r - ζ.1 ^ (f0 u).val) := by
    intro u
    rw [hf0def]
    exact Classical.choose_spec (hex u)
  have hf0_iff : ∀ u a, f0 u = a ↔ u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u a
    constructor
    · rintro rfl
      exact hf0 u
    · intro ha
      by_contra hne
      exact (hf0 u) (huniq u a (f0 u) (Ne.symm hne) ha)
  have hloc : IsLocallyConstant f0 := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    have hfib : f0 ⁻¹' {a} = ⋂ b ∈ (Finset.univ.erase a : Finset (ZMod q)), (U.basicOpen (r - ζ.1 ^ b.val) : Set U) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ,
        and_true, SetLike.mem_coe]
      rw [hf0_iff]
      constructor
      · intro ha b hb
        exact huniq u a b (Ne.symm hb) ha
      · intro h ha
        obtain ⟨a', ha'⟩ := hex u
        by_cases heq : a' = a
        · exact ha' (heq ▸ ha)
        · exact ha' (h a' heq)
    rw [hfib]
    exact isOpen_biInter_finset fun b _ => (U.basicOpen (r - ζ.1 ^ b.val)).isOpen
  refine ⟨⟨f0, hloc⟩, ?_, fun u a ha => (hf0_iff u a).mpr ha⟩
  delta CrystallineSemistableComparison.E.IsPow
  intro V g a hga
  have hunitb : ∀ b : ZMod q, b ≠ a → IsUnit (g.appTop.hom (r - ζ.1 ^ b.val)) := fun b hb =>
    isUnit_appTop_of_mem g _ (fun v => huniq (g v) a b (Ne.symm hb) ((hf0_iff (g v) a).mp (hga v)))
  have hprodV : ∏ b : ZMod q, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val) = 0 := by
    have h0 := congrArg g.appTop.hom hprod
    rw [map_prod, map_zero] at h0
    simpa only [map_sub, map_pow] using h0
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)] at hprodV
  have hu : IsUnit (∏ b ∈ Finset.univ.erase a, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one (fun b hb => ?_)
    have h1 := hunitb b (Finset.ne_of_mem_erase hb)
    simpa only [map_sub, map_pow] using h1
  have h0 : g.appTop.hom r - g.appTop.hom ζ.1 ^ a.val = 0 := hu.mul_left_eq_zero.mp hprodV
  show g.appTop.hom r = (g.appTop.hom ζ.1) ^ a.val
  exact sub_eq_zero.mp h0

theorem rootPow : CrystallineSemistableComparison.E.PrimAlg → CrystallineSemistableComparison.E.RootPow := by
  intro hP q _ U ζ
  refine ⟨fun r hr => ?_, fun ξ => ?_⟩
  · obtain ⟨f, hf, -⟩ := exists_isPow hP q U ζ r hr
    exact ⟨f, hf⟩
  · have hξq : ξ.1 ^ q = 1 := (hP q _ ξ).1
    obtain ⟨f, hf, hloc⟩ := exists_isPow hP q U ζ ξ.1 hξq
    refine ⟨f, hf, fun u => ?_⟩
    have hprod : ∏ a : ZMod q, (ξ.1 - ζ.1 ^ a.val) = 0 := by
      rw [← (hP q _ ζ).2.2.1 ξ.1, hξq, sub_self]
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ
      (fun a : ZMod q => ξ.1 - ζ.1 ^ a.val) hprod u
    rw [hloc u a ha]
    by_contra hna
    set m := a.val with hm
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have ha' : a = (m : ZMod q) := (ZMod.natCast_zmod_val a).symm
    have hcop : ¬ m.Coprime q := by
      intro hc
      exact hna (ha' ▸ (ZMod.isUnit_iff_coprime m q).2 hc)
    set g := Nat.gcd m q with hgdef
    have hg1 : g ≠ 1 := hcop
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right m hq
    have hgq : g ∣ q := Nat.gcd_dvd_right m q
    have hgm : g ∣ m := Nat.gcd_dvd_left m q
    set k := q / g with hkdef
    have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hklt : k < q := Nat.div_lt_self hq (by omega)
    have hζq : ζ.1 ^ q = 1 := (hP q _ ζ).1
    have hζmk : (ζ.1 ^ m) ^ k = 1 := by
      obtain ⟨m', hm'⟩ := hgm
      have e1 : m * k = q * m' := by
        rw [hm', hkdef, mul_comm g m', mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
      rw [← pow_mul, e1, pow_mul, hζq, one_pow]
    have hunit : IsUnit (ξ.1 ^ k - 1) := by
      have hne : ((k : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        exact absurd (Nat.le_of_dvd hkpos hd) (by omega)
      have hu := (hP q _ ξ).2.1 (k : ZMod q) 0 hne
      rwa [ZMod.val_natCast_of_lt hklt, ZMod.val_zero, pow_zero] at hu
    have hdvd : ξ.1 - ζ.1 ^ m ∣ ξ.1 ^ k - 1 := by
      have hs := sub_dvd_pow_sub_pow ξ.1 (ζ.1 ^ m) k
      rwa [hζmk] at hs
    apply ha
    rw [Scheme.mem_basicOpen_top]
    exact isUnit_of_dvd_unit (map_dvd _ hdvd) (hunit.map _)

end GlobalTheory.CompanionTheory.RootPowLC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEvCongr
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC
open CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem mul_ev_congr {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k s t : ℤ}
    (h : n + m = k) (hst : s + t = k) (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m) :
    μ.mul X s t k hst (ev α 0 s hs X (𝟙 X)) (ev β 0 t ht X (𝟙 X)) =
      μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  obtain rfl : s = n := by simpa using hs.symm
  obtain rfl : t = m := by simpa using ht.symm
  rfl

theorem aw_value {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k : ℤ}
    (h : n + m = k) (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m)
    (γ : Cochain ((chains R).obj (sch.obj X)) K k) (hγ : μ.IsAW h α β γ) :
    ev γ 0 k (by simp) X (𝟙 X) = μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  have h0 := hγ 0 k (by simp) X (𝟙 X)
  rw [Fin.sum_univ_one] at h0
  rw [h0]
  have hu : (m * ((0 : Fin 1) : ℕ)).negOnePow = 1 := by simp
  rw [hu, one_smul]
  exact mul_ev_congr μ h _ _ _ α β

theorem repCup : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepCup := by
  intro _ _ _ _ _ R _ I J K μ X n m k h x y a b hx hy
  obtain ⟨α, rfl, rfl⟩ := hx
  obtain ⟨β, rfl, rfl⟩ := hy
  obtain ⟨γ, hγ⟩ := μ.aw_exists (sch.obj X) h α β
  exact ⟨γ, (μ.cup_spec (sch.obj X) h α β γ hγ).symm, aw_value μ h α.1 β.1 γ.1 hγ⟩

end GlobalTheory.CompanionTheory.EdgeRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCZsmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMapPull

universe w w' w₁ w₁' u v u' v'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w'} R} {F' : C' ⥤ ModuleCat.{w₁'} R'}
  {T : Res.{w} F} {T' : Res.{w₁} F'} {m : Mor F F' σ}

theorem d_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    d (T'.K s) k (n.pullC s k x) = n.pullC s (k + 1) (d (T.K s) k x) := by
  funext t
  change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((T'.K s).map (GlobalTheory.CatH.toLast i t)).hom
      (n.τ s _ (x (GlobalTheory.CatH.face i t ⋙ m.G))) =
    n.τ s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((T.K s).map (m.G.map (GlobalTheory.CatH.toLast i t))).hom (x (GlobalTheory.CatH.face i t ⋙ m.G)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, n.nat]

theorem dvC_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    T'.dvC s k (n.pullC s k x) = n.pullC (s + 1) k (T.dvC s k x) :=
  funext fun t => (n.dv s _ (x (t ⋙ m.G))).symm

theorem ιC_pullC (n : ResMor T T' m) (k : ℕ) (z : Cn F k) :
    T'.ιC k (m.pullC k z) = n.pullC 0 k (T.ιC k z) :=
  funext fun t => (n.ι _ (z (t ⋙ m.G))).symm

theorem pullC_zsmul (n : ResMor T T' m) (s k : ℕ) (c : ℤ) (x : Cn (T.K s) k) :
    n.pullC s k (c • x) = c • n.pullC s k x :=
  funext fun t => map_zsmul (n.τ s _) c (x (t ⋙ m.G))

theorem st_pullC (n : ResMor T T' m) {j : ℕ} (z : Cn F j) :
    ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T'.St (m.pullC j z) s k (n.pullC s k x) := by
  intro s
  induction s with
  | zero =>
    intro k x h
    simp only [Res.St] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, ιC_pullC n j z⟩
  | succ s ih =>
    intro k x h
    simp only [Res.St] at h ⊢
    obtain ⟨a, rfl, ha⟩ := h
    refine ⟨n.pullC s k a, dvC_pullC n s k a, ?_⟩
    have := ih (k + 1) _ ha
    rwa [pullC_zsmul, ← d_pullC] at this

end GlobalTheory.CompanionTheory.EdgeMapPull


open GlobalTheory.CompanionTheory.EdgeMapPull in
theorem GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap : CrystallineSemistableComparison.E.EdgeMap := by
  intro R R' _ _ σ C C' _ _ F F' T T' m n j x h hE
  obtain ⟨z, hz, hS, rfl⟩ := hE
  exact ⟨m.pullC j z, by rw [m.d_pullC, hz, map_zero], st_pullC n z j 0 x hS, rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedResMor
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeRed

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom x) h).symm

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C']

def redResMor (hS : KapSpec) (hK : KapRed) (hR : InRed) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q)
    (P : Probe C Q) (P' : Probe C' q) (m : Mor P.L P'.L (RingHom.id ℤ))
    (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (hτ : ∀ c (f : LocallyConstant (P.U (m.G.obj c)) (ZMod Q)),
      m.τ c f = lcRes q (g c) (f.map (ZMod.castHom h (ZMod q))))
    (hζ : ∀ c, (P'.ζ c).1 = (primRes (g c) (P.ζ _)).1 ^ (Q / q)) (i : ℤ) :
    ResMor (P.res i) (P'.res i) m where
  τ s c :=
    { toFun := fun x => Sec.res (g c) ((redMap Q q i).app (P.U (m.G.obj c)) (s : ℤ) x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  nat s {c c'} φ x := by
    change Sec.res (g c') ((redMap Q q i).app _ (s : ℤ) (Sec.res (P.S.map (m.G.map φ)).unop x)) =
      Sec.res (P'.S.map φ).unop (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).nat, res_res, res_res, hg]
  ι c x := by
    change Sec.res (g c) ((redMap Q q i).app _ 0 (Sec.map (resι _ (tw Q i)) (kap i (P.ζ (m.G.obj c)) x))) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [(redMap Q q i).nat, res_map, (hS Q i _ (P.ζ (m.G.obj c)) x).2.2 _ (g c),
      hK hR Q q h i _ (primRes (g c) (P.ζ (m.G.obj c))) (P'.ζ c) (hζ c), hτ]
    rfl
  dv s c x := by
    change Sec.res (g c) ((redMap Q q i).app _ ((s + 1 : ℕ) : ℤ) (Sec.map ((GlobalTheory.EtC.res _ (tw Q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x)) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) ((redMap Q q i).app _ (s : ℤ) x))
    rw [← (redMap Q q i).comm, res_map]

theorem etRed : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.KapSpec →
    CrystallineSemistableComparison.E.KapRed → CrystallineSemistableComparison.E.EtRed := by
  intro hSpec hEdge hRep hOpR hS hK hGen hR hOp Q q _ _ h C C' _ _ P P' X Y Y' m g hg hτ hy hζ i j x
  obtain ⟨a, ha⟩ := (hRep _ _ X (j : ℤ)).1 x
  have hE := (hSpec hGen Q C P X Y i j x).1 a ha
  have hE' := hEdge ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m
    (redResMor hS hK hR h P P' m g hg hτ hζ i) j _ _ hE
  have hr : Rep (red Q q _ (j : ℤ) i x) ((redMap Q q i).app X (j : ℤ) a) :=
    hOpR hOp _ _ _ _ (redMap Q q i) X (j : ℤ) x a ha
  refine (hSpec hGen q C' P' X Y' i j (red Q q _ (j : ℤ) i x)).2 _ ⟨_, hr, ?_⟩
  convert hE' using 1
  funext t
  change Sec.res (Y'.y _) ((redMap Q q i).app X (j : ℤ) a) =
    Sec.res (g _) ((redMap Q q i).app _ (j : ℤ) (Sec.res (Y.y _) a))
  rw [← (redMap Q q i).nat, res_res, hy]

end GlobalTheory.CompanionTheory.EdgeRed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StAdd
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairAdd

theorem stAdd : CrystallineSemistableComparison.E.StAdd := by
  intro R _ C _ F T j z z' s
  induction s with
  | zero =>
    intro k x x' hx hx'
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨h', rfl⟩ := hx'
    subst h
    exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩⟩
  | succ s ih =>
    intro k x x' hx hx'
    obtain ⟨a, rfl, ha⟩ := hx
    obtain ⟨a', rfl, ha'⟩ := hx'
    obtain ⟨h1, h2⟩ := ih (k + 1) _ _ ha ha'
    refine ⟨⟨a + a', by simp, ?_⟩, ⟨a - a', by simp, ?_⟩⟩
    · simpa [map_add (f := _), smul_add] using h1
    · simpa [map_sub, smul_sub] using h2

end GlobalTheory.CompanionTheory.StairAdd
end

