module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullAll
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem isThetaPt_comp {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) (f : I' → I) : IsThetaPt P k (fun i => x (f i)) fun i => v (f i) := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4,
    fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩

theorem isThetaPt_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : IsThetaPt P k x v) : IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4,
    a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso D k Q act e) (M r : ℕ) (a : D.La) : I.ev M (r • a) = I.ev M a ^ r := by
  induction r with
  | zero =>
    have := I.add M 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem theta_down (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] (o : Full D K) {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    {v v' : D.La → K} (c : Kˣ) (hc : ∀ x, v (r • x) = c * v' x) (h : o.Theta (r * m) v) : o.Theta m v' := by
  have e : ∀ a, o.I.ev ((r * m) ^ 2) (r • a) ^ r = o.I.ev (m ^ 2) a := fun a => by
    rw [ev_nsmul, ← pow_mul, ← o.I.tower (m ^ 2) (r * r) (by positivity) (by positivity)]
    congr 2; ring
  have h₁ := _root_.GlobalTheory.ThetaNest.isThetaPt_down hL K o.P r m D.La _ _ (fun a => by
    rw [e]; exact (o.I.onto _ (by positivity) _).2 ⟨a, rfl⟩) (isThetaPt_comp h fun a => r • a)
  have h₂ := isThetaPt_mul (fnOf ((c⁻¹ : Kˣ) : K)) ((c⁻¹).isUnit.map _) h₁
  simp only [e] at h₂
  unfold Full.Theta
  convert h₂ using 2 with a
  rw [hc]
  exact (congrArg fnOf (Units.inv_mul_cancel_left c (v' a)).symm).trans (map_mul _ _ _)

theorem exists_iso (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) (D : Datum H) {n : ℕ}
    (hn : n.Prime) (ho : Odd n) : ∃ J₀, ∀ J, J₀ ≤ J → ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (v : D.La → K),
      o.I.ζ ((n ^ J) ^ 2) = o'.I.ζ ((n ^ J) ^ 2) → o.Theta (n ^ J) v → o'.Theta (n ^ J) v →
      ∃ φ : o.P.A ≅ o'.P.A, IsPolIso o.P o'.P φ ∧
        (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) := by
  letI := H.starRing
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  generalize Module.finrank ℚ E / 2 * (D.p + D.q) = g at bas hbas
  choose cn hcn using exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  let B := ((n ^ 2) ^ 2) ^ g * g.factorial + 4 ^ g * g.factorial * (2 * s.sup cn)
  refine ⟨B + 4, fun J hJ K _ _ o o' v hζ hv hv' => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : B < n ^ (j + 4) := lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hp : 0 < n ^ (j + 4) := pow_pos hn.pos _
  set M := (n ^ (j + 4)) ^ 2 with hM
  have hM0 : 0 < M := pow_pos hp _
  haveI : NeZero M := ⟨hM0.ne'⟩
  haveI := o.charZero
  obtain ⟨hg, lev, hb, hl⟩ := _root_.GlobalTheory.exists_level_of_full hL E H D g bas hbas K o M hM0
  have Q := _root_.GlobalTheory.exists_level_of_full hL E H D g bas hbas K o' M hM0
  rw [← hζ] at Q
  obtain ⟨hg', lev', hb', hl'⟩ := Q
  let lab : (Fin (2 * g) → ZMod M) → D.La := fun a => bas fun i => ((a i).val : ℤ)
  have hlab : ∀ a : Fin (2 * g) → ZMod M, (fun i => (((a i).val : ℤ) : ZMod M)) = a := fun a => funext fun i => by simp
  have e : levelPoint lev hg = fun a => o.I.ev M (lab a) := funext fun a => by rw [← hl, hlab]
  have e' : levelPoint lev' hg' = fun a => o'.I.ev M (lab a) := funext fun a => by rw [← hl', hlab]
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ B := le_add_left (by gcongr)
      _ < n ^ (j + 4) := hB
      _ ≤ M := Nat.le_self_pow two_ne_zero _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  obtain ⟨φ, hφ, hφb⟩ := h₁ g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) (lt_of_le_of_lt (Nat.le_add_right _ _) hB) K
    (Nat.cast_ne_zero.2 hn.pos.ne') o.P o'.P hg hg' _ lev lev' (fun a => fnOf (v (lab a)))
    (e ▸ isThetaPt_comp hv lab) (e' ▸ isThetaPt_comp hv' lab)
  haveI := hφ.1
  have hev : ∀ a, o.I.ev M a ≫ φ.hom = o'.I.ev M a := fun a => by
    obtain ⟨c, rfl⟩ := bas.surjective a
    rw [← hl, ← hl', ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]
    exact congrArg (linComb · _) (funext hφb)
  refine ⟨φ, hφ, fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (s : Set (𝓞 E)) := hs ▸ Submodule.mem_top
  have add : ∀ a b, o.oa.act (a + b) = o.oa.act a * o.oa.act b := o.oa.map_add
  have add' : ∀ a b, o'.oa.act (a + b) = o'.oa.act a * o'.oa.act b := o'.oa.map_add
  let f : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (o.oa.act a ≫ φ.hom))
    fun a b => by rw [add, MonObj.mul_comp]; rfl
  let f' : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (φ.hom ≫ o'.oa.act a))
    fun a b => by rw [add', MonObj.comp_mul]; rfl
  have : f = f' := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha => by
    refine congrArg Additive.ofMul (h₂ g (cn a) M (key _ (Finset.le_sup ha)) K (Nat.cast_ne_zero.2 hM0.ne') o.P o'.P hg hg'
      φ hφ _ o.oa o'.oa a (hcn a) fun y hy => ?_)
    obtain ⟨b, rfl⟩ := (o.I.onto M hM0 y).1 hy
    have l := o.I.lin M a b
    have l' := o'.I.lin M a b
    rw [← Category.assoc, ← Category.assoc, ← l, hev, hev, l']
  exact Additive.ofMul.injective (DFunLike.congr_fun this x)

theorem exists_full_all (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) {K : Type} [Field K]
    [IsAlgClosed K] (ρ : K) (ζ : ℕ → Kˣ) (hζ : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) (v : ℕ → D.La → K)
    (hv : ∀ r m, Odd r → Odd m → ∃ c : Kˣ, ∀ x, v (r * m) (r • x) = c * v m x) {n : ℕ} (hn : n.Prime) (ho : Odd n)
    (h : ∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = ρ ∧ o.I.ζ ((n ^ j) ^ 2) = ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (v (n ^ j))) :
    ∃ o : Full D K, o.ρ = ρ ∧ ∀ j, o.I.ζ (n ^ j) = ζ (n ^ j) ∧ o.Theta (n ^ j) (v (n ^ j)) := by
  obtain ⟨J, hJ⟩ := exists_iso hL h₁ h₂ D hn ho
  choose o hρ hz ht using fun j => h (J + 2 + j) (by omega)
  have hp : ∀ i, 0 < n ^ i := fun i => pow_pos hn.pos i
  have th : ∀ j i, i ≤ J + 2 + j → (o j).Theta (n ^ i) (v (n ^ i)) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hi
    obtain ⟨c, hc⟩ := hv (n ^ d) (n ^ i) ho.pow ho.pow
    refine theta_down hL (o j) (hp d) (hp i) c hc ?_
    rw [← pow_add, ← hd]; exact ht j
  have ze : ∀ j i, i ≤ 2 * (J + 2 + j) → (o j).I.ζ (n ^ i) = ζ (n ^ i) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    have := hz j
    rw [← pow_mul, mul_comm, hd, pow_add] at this
    rw [← (o j).I.ζ_pow _ _ (hp i) (hp d), this, hζ _ _ (hp i) (hp d)]
  have ze' : ∀ j i, i ≤ J + 2 + j → (o j).I.ζ ((n ^ i) ^ 2) = ζ ((n ^ i) ^ 2) := fun j i hi => by
    rw [← pow_mul]; exact ze j _ (by omega)
  choose φ hφ hact using fun j => hJ (J + 2) (by omega) K (o j) (o 0) _
    ((ze' j _ (by omega)).trans (ze' 0 _ le_rfl).symm) (th j _ (by omega)) (th 0 _ le_rfl)
  choose I hIζ _ hI using fun j => GlobalTheory.T.exists_tateIso_of_isPolIso hL E H D K (o j) (o 0) (φ j) (hφ j) (hact j)
  obtain ⟨I', hI'⟩ := _root_.GlobalTheory.Ex.TateLimit.exists_limit E H D K _ _ _ I
  refine ⟨{ o 0 with I := I' }, hρ 0, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj, -, e⟩ := hI' _ (hp i) i
    exact e.trans ((congrFun (hIζ j) _).trans (ze j i (by omega)))
  · obtain ⟨j, hj, e, -⟩ := hI' _ (pow_pos (hp i) 2) i
    have := hI j _ _ (th j i (by omega))
    unfold Full.Theta at this ⊢
    dsimp only at this ⊢
    rw [e]; exact this

end GlobalTheory.Ex.AllLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_normalised_unit (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b c : ℤ)
    (hc : c = a - b)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (d : Γ(T.left, ⊤)ˣ),
      α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T c) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val α r z J = gm (r ≫ (fst T A).left) z ⊤ d * val α₀ r z J := by
  have hγ := DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ (ptSecT A 1).left)) (NormTheta.rigT_isGen (T := T) hρ c)
  obtain ⟨d, hd⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero]) hγ
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T c)) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ hγ _))
  refine ⟨α, d, hα, corr_of_val hL fun y J hJ => ?_, fun Z r z J hJ => ?_⟩
  · rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormTheta.ptSec_fst, Category.comp_id,
      val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]
  · rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, hd _ _ z J hJ, Category.comp_id, mul_comm]

theorem isGenSec_smul {k : ℤ} {th : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (e : Γ(T.left, ⊤)ˣ) :
    IsGenSec A L k (SecM.toSec A ((e : Γ(T.left, ⊤)) • SecM.ofSec A th)) := fun s => by
  obtain ⟨r, hr⟩ := H s
  have e₁ : SecM.ofSec A s = r • SecM.ofSec A th := Subtype.ext (funext hr)
  have e₂ : SecM.ofSec A s = (r * (e⁻¹ : Γ(T.left, ⊤)ˣ)) • ((e : Γ(T.left, ⊤)) • SecM.ofSec A th) := by
    rw [← mul_smul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one, e₁]
  exact ⟨_, fun j => congrArg (fun q => q.1 j) e₂⟩

theorem exists_thG (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a : ℤ)
    (ha : a = ((m ^ 2 : ℕ) : ℤ)) {I : Type} {x : I → (T ⟶ A)} (hx : ∀ i, x i ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) T)} {s₁ : LB.Sec (LPow A L a T)}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ A).left) (fun _ => a))}
    {U : I → ThetaGrp A L a T} {s₂ : I → LB.Sec (LPow A L a T)} {w : I → Γ(T.left, ⊤)}
    (hα : α.IsGen) (hτ : τ.IsGen)
    (h₁ : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a ((1 : ℕ) : ℤ) α th s₁)
    (hU : ∀ i, SymLift A L a (m ^ 2) (x i) (U i)) (h₂ : ∀ i, IsActOf A L a (U i) s₁ (s₂ i))
    (hw : ∀ i, IsValueAt A L a (s₂ i) 1 τ (w i)) :
    ∃ e : Γ(T.left, ⊤)ˣ, ∀ i, ThG A L ρ m th (x i) (e * w i) := by
  subst ha
  obtain ⟨α', d, hα', hn, hv⟩ := exists_normalised_unit hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α hα
  obtain ⟨b, hb⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, NormTheta.one_left, zpow_neg,
        mul_inv_cancel])
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (NormTheta.rigT_isGen (T := T) hρ ((m ^ 2 : ℕ) : ℤ))))
  refine ⟨d * b, fun i => ⟨hx i, SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i)), α',
    SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁), U i, hα', hn, ?_, hU i, ?_, fun y J hJ => ?_⟩⟩
  · refine VVRank.isTwistPull_of_sv A hL hα' fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A h₁ (𝟙 _) y hJ, hv _ _ y J hJ, gs_unit _ _ ⊤ trivial, Units.val_mul, _root_.mul_assoc]
  · refine VVRank.isTwistPull_of_sv A hL (U i).isGen fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A (h₂ i) (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, translT, lift_fst, mul_left_comm]
  · have q := ThetaPtMove.sv_of_isValueAt (hw i) (𝟙 _) y hJ
    have q' := hb _ (𝟙 _) y J hJ
    rw [val_mul hJ, val_inv, Category.comp_id, mul_inv_eq_iff_eq_mul] at q'
    rw [Category.id_comp, q', Units.val_mul, ← gs_unit _ _ ⊤ trivial] at q
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      q, ptSecT_fst, Units.val_mul, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial]
    ring

end

theorem exists_gen_thG_of_isThetaPt : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))), ρ.IsGen → ∀ (m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ i, x i ^ (m ^ 2) = 1) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))), IsGenSec P.A P.L ((1 : ℕ) : ℤ) th ∧ ∀ i, ThG P.A P.L ρ m th (x i) (fnOf (v i)) := by
  intro K _ P ρ hρ m Ix x v hx H
  have : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, h₁, hU, h₂, hw, hv⟩ := ThetaCoord.isThetaPtOver_of_subsingleton P H
  obtain ⟨e, he⟩ := exists_thG P.isLB hρ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hx (th := th) (α := α) hα hτ h₁ hU h₂ hw
  refine ⟨_, isGenSec_smul hth (u * e⁻¹), fun i => ?_⟩
  have q := ThG.smul P.isLB (a := ((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)))
    (th' := SecM.toSec P.A (((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)) • SecM.ofSec P.A th))
    rfl (he i)
  rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, ← hv i] at q
  exact q

end GlobalTheory.Ex.OneGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricallyConnectedAwayOfGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GenSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.ConnFibre

theorem exists_geometricallyConnected : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Smooth f → GlobalTheory.AbLaw.IsProjBy f → GeometricallyConnected f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → GeometricallyConnected f' := by
  intro R K _ _ _ _ _ _ X X₀ f f₀ φ hb hs hp hc
  obtain ⟨P⟩ := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy R X f hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R X f hp
  let L := AlgebraicClosure K
  let g₀ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hg₀ : Function.Injective g₀ := (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  let y₀ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  have h₀ : IsPullback (pullback.fst f₀ y₀ ≫ φ) (pullback.snd f₀ y₀) f
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback f₀ y₀).paste_horiz hb
    erw [← Spec.map_comp] at this
    exact this
  have hs₀ : Smooth f₀ := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f₀ hs₀ hc
  have hint : IsIntegral (pullback f₀ y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback f₀ y₀)
  have hpr₀ : IsProper (pullback.snd f₀ y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback f₀ y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst f₀ y₀ ≫ φ) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hsurj : Surjective f := by
    have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hbot : (⊥ : PrimeSpectrum R) ∈ Set.range f := by
      refine ⟨(pullback.fst f₀ y₀ ≫ φ) x₀, ?_⟩
      have e : f ((pullback.fst f₀ y₀ ≫ φ) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd f₀ y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext (le_bot_iff.1 fun a ha => ?_))
      have ha' : g₀ a ∈ (pullback.snd f₀ y₀ x₀).asIdeal := ha
      by_contra hne
      have hne' : g₀ a ≠ 0 := fun h => hne (hg₀ (h.trans (map_zero g₀).symm))
      exact (PrimeSpectrum.isPrime (pullback.snd f₀ y₀ x₀)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ ha' (IsUnit.mk0 _ hne'))
    refine ⟨fun z => ?_⟩
    have hsp : (⊥ : PrimeSpectrum R) ⤳ (z : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    exact hsp.mem_closed hcl hbot
  refine ⟨δ, fun h => hδ (h ▸ map_zero g₀), fun R' _ g hg X' π f' hπ => ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have h' : IsPullback (fst ≫ π) snd f (Spec.map (CommRingCat.ofHom ((algebraMap R' F).comp g))) := by
    have := h.paste_horiz hπ
    erw [← Spec.map_comp] at this
    exact this
  have : Surjective snd := MorphismProperty.of_isPullback h' hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h' _ (hker F _ (hg.map (algebraMap R' F)))
  exact ⟨⟨z⟩⟩

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMinOn
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.OneBasis.AdaptedFamily

theorem exists_min_on {X : Type} {Q : X → ℤ} (h : ∀ x, 0 ≤ Q x) {s : Set X} (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, Q x ≤ Q y := by
  obtain ⟨x, hx, hm⟩ := (wellFounded_lt (α := ℕ)).has_min ((fun x => (Q x).toNat) '' s) (hs.image _)
  obtain ⟨x, hx, rfl⟩ := hx
  refine ⟨x, hx, fun y hy => ?_⟩
  have h₁ : ¬ (Q y).toNat < (Q x).toNat := hm _ ⟨y, hy, rfl⟩
  have h₂ := h x
  have h₃ := h y
  omega

theorem main : LL → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α), AdFam D Q k cls mu f ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (i : Fin r), ∃ s : Fam D.toPre F k, GlobalTheory.ZH.FamOf D.toPre F (f i) s := by
  classical
  intro hL V _ _ _ ϖ hϖ D Q hQ k hk
  have hQ0 : ∀ χ, 0 ≤ Q χ := fun χ => by
    by_cases h : χ = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · have := QForm.Q_pos hϖ D hQ h; omega
  let C := D.toPre.X ⧸ FamFree.multiples D.toPre k
  have hc : Nat.card C = k ^ Module.finrank ℤ D.toPre.X := AddSubgroup.index_range_nsmul D.toPre.X k
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite C
  let e : Fin (Fintype.card (C × Fin (k ^ D.toPre.P.g))) ≃ C × Fin (k ^ D.toPre.P.g) := (Fintype.equivFin _).symm
  choose rep hrep hmin using fun c : C => exists_min_on hQ0
    (s := {α | (QuotientAddGroup.mk α : C) = c}) ⟨c.out, c.out_eq⟩
  have hQmin : ∀ c z, Q (rep c) ≤ Q (rep c + k • z) := fun c m =>
    hmin c _ (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, rfl⟩).symm.trans (hrep c))
  choose b hb using fun c => AdaptedBasis.exists_isBasisB hL.2.1.secTwist D.toPre hk (rep c)
  choose Φ f hΦ hf hz using fun c m =>
    AdaptedBasis.integralFamily_of_min hL.1.globalFns hϖ hQ hk (rep c) (b c m) (hQmin c)
  have inj : ∀ c c', rep c = rep c' → c = c' := fun c c' h => (hrep c).symm.trans (by rw [h]; exact hrep c')
  let ε : ∀ i₀, {i // rep (e i).1 = rep (e i₀).1} ≃ Fin (k ^ D.toPre.P.g) := fun i₀ =>
    { toFun := fun i => (e i.1).2
      invFun := fun m => ⟨e.symm ((e i₀).1, m), by rw [Equiv.apply_symm_apply]⟩
      left_inv := fun i => Subtype.ext (e.symm_apply_eq.2 (Prod.ext (inj _ _ i.2).symm rfl))
      right_inv := fun m => by simp }
  refine ⟨_, fun i => rep (e i).1, k ^ D.toPre.P.g, fun i => f (e i).1 (e i).2,
    ⟨⟨fun i => hQmin _, fun i i' ⟨m, hm⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩, fun i => ⟨_, hΦ _ _⟩, fun i => hz _ _,
      fun i₀ => ?_⟩, fun F _ _ i => FamBaseChange.main hL.1.globalFns V _ D k _ _ (hΦ _ _) F⟩
  · exact congrArg rep ((hrep _).symm.trans (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, hm.symm⟩).symm.trans (hrep _)))
  · obtain ⟨m, hm⟩ := (FamFree.mk_eq_mk_iff _ _).1 (hrep (QuotientAddGroup.mk α))
    refine ⟨e.symm (QuotientAddGroup.mk α, ⟨0, by positivity⟩), m, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hm.symm
  · exact (Nat.card_congr (ε i₀)).trans (Nat.card_fin _)
  · refine AdaptedBasis.isBasisB_reindex (ε i₀) (hb (e i₀).1) fun i => ?_
    have key : ∀ c c' m, c = c' → f c m (rep c') = b c' m := by
      rintro c _ m rfl; exact hf c m
    exact key _ _ _ (inj _ _ i.2)

end GlobalTheory.OneBasis.AdaptedFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.GoodTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_point {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ)
    {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = x ≫ χ) : PolAt t x := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull x t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t' : SAB H (Sp K)) (p : Sp K ⟶ Y.X) (_ : p = y ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t y) := by
    intro t' p hp n
    subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ hy.symm n
  have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (Y.oF.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper,
    amplePt _ _ y _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) h₂.symm h₃) Y.oF.ample Y.oF.ktriv⟩

theorem splitOver_of_abLocus {W : Type} [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (h : ∀ x, x ∈ abLocus G) : GlobalTheory.LN.SplitOver G (maximalIdeal W) := by
  letI := Ideal.Quotient.field (maximalIdeal W)
  have p : Spec (CommRingCat.of (W ⧸ maximalIdeal W)) := (default : PrimeSpectrum _)
  have hp := ArcNotAbelian.isProper_fibre G hG (W ⧸ maximalIdeal W) (spMap (Ideal.Quotient.mk (maximalIdeal W))) p (h _)
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have hab : IsAbelianScheme ((Over.pullback (spMap (Ideal.Quotient.mk (maximalIdeal W)))).obj G) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), hp,
      inferInstanceAs (GeometricallyConnected (pullback.snd _ _))⟩
  unfold GlobalTheory.LN.SplitOver
  exact ⟨_, ZJ.isGt_splitExtOfAbelian _ hab⟩

theorem exists_pelUnif_subsingleton : LL → UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ Y.j = jK W ≫ χ → Set.range χ ⊆ abLocus Y.t.G → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Subsingleton P.D.toPre.X := by
  intro _ hU E _ _ _ H D l Xo c O _ β Y W _ _ _ hW χ y hy hab
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp W), Nonempty (SABMap t Y.t χ) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull χ Y.t
    exact ⟨_, ⟨m⟩⟩
  have ht : ∀ x, x ∈ abLocus t.G := fun x => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 x).1 (hab ⟨x, rfl⟩)
  obtain ⟨P, -⟩ := hU E H W hW t (polAt_of_point Y m _ y hy) (splitOver_of_abLocus t.G t.semi ht)
  refine ⟨t, m, P, ?_⟩
  have hmax : (maximalIdeal W ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (W ⧸ maximalIdeal W ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (W ⧸ maximalIdeal W ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (W ⧸ maximalIdeal W ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick W (maximalIdeal W) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom

end GlobalTheory.GoodTrait
end

