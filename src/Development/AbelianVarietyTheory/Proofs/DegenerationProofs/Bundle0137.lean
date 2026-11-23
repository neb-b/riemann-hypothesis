module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

namespace GlobalTheory.Ex.FibIso

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

def Reads {F : Type} [Field F] (B : NumB F) (Q : PolAV (Sp F)) (E : B.A ≃* (baseOver (Sp F) ⟶ Q.A)) : Prop :=
  (∀ k : ℕ, 1 ≤ k → ∀ b b' : B.A, b ^ k = 1 → b' ^ k = 1 →
    WeilIs Q.A Q.L k (E b) (E b') (unitOn (B.weil k b b'))) ∧
  ∀ m : ℕ, Odd m → (m : F) ≠ 0 → ∀ (Ix : Type) (b : Ix → B.A), (∀ i, b i ^ m ^ 2 = 1) →
    IsThetaPt Q m (fun i => E (b i)) (fun i => fnOf (B.uth m (b i) 1))

theorem exists_reads (hU : BrUthSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (h₁ : D.PsiEven)
    (h₂ : D.TauBimult) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {N : NumD F}
    (ν : NumOf D F N) {Q : PolAV (Sp F)} {Φ : Q.A.left ⟶ D.P.A.left} (hΦ : IsFib D F Q Φ) :
    ∃ E : N.A ≃* (baseOver (Sp F) ⟶ Q.A), (∀ b, (ν.eA b).left = (E b).left ≫ Φ) ∧ Reads N.toNumB Q E := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hΦ.1 (𝟙 (Sp F)) (TF (R := R) F).hom (Category.id_comp _).symm
  obtain ⟨w, t⟩ := hU R D h₁ h₂ F N ν
  have hE : ∀ b, (ν.eA b).left = ((ν.eA.trans e.symm) b).left ≫ Φ := fun b =>
    (congrArg (fun z => z.left) (e.apply_symm_apply (ν.eA b)).symm).trans (he _)
  refine ⟨ν.eA.trans e.symm, hE, fun k hk b b' hb hb' => ?_, fun m hm hm' Ix b hb => ?_⟩
  · have key : ∀ (s : Sp F ⟶ Sp R) (_ : s = 𝟙 _ ≫ (TF (R := R) F).hom) (x y : baseOver (Sp F) ⟶ Q.A)
        (x₀ y₀ : Over.mk s ⟶ D.P.A) (c : Γ(Sp F, ⊤)ˣ), x₀.left = x.left ≫ Φ → y₀.left = y.left ≫ Φ →
        WeilIs D.P.A D.P.L k x₀ y₀ c → WeilIs Q.A Q.L k x y c := by
      rintro s rfl x y x₀ y₀ c hx hy h
      have := Q.isAb.comm
      exact (weilIs_grpPullback_of_comm' _ _ _ _ _ Φ _ _ D.P.isLB Q.isLB hΦ.1 hΦ.2.1 (baseOver _) k x y x₀ y₀ c
        hx hy).2 h
    exact key _ (Category.id_comp _).symm _ _ _ _ _ (hE b) (hE b') (w k hk b b' hb hb')
  · have key : ∀ (s : Sp F ⟶ Sp R) (_ : s = 𝟙 _ ≫ (TF (R := R) F).hom) (x : Ix → (baseOver (Sp F) ⟶ Q.A))
        (x₀ : Ix → (Over.mk s ⟶ D.P.A)) (v : Ix → Γ(Sp F, ⊤)), (∀ i, (x₀ i).left = (x i).left ≫ Φ) →
        (∀ i, x i ^ m ^ 2 = 1) → IsThetaPt D.P m x₀ v → IsThetaPt Q m x v := by
      rintro s rfl x x₀ v hx hp h
      exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp F)) hΦ.1 hΦ.2.1 hx hp _).2 h
    exact key _ (Category.id_comp _).symm _ _ _ (fun i => hE (b i))
      (fun i => by rw [← map_pow, hb, map_one]) (t m hm hm' Ix b hb).1

theorem linComb_map {S : Scheme.{0}} {A T : Over S} [GrpObj A] {G : Type} [Group G] (f : G →* (T ⟶ A)) {r : ℕ}
    (y : Fin r → G) (a : Fin r → ℕ) :
    linComb (fun i => f (y i)) a = f (List.ofFn fun i => y i ^ a i).prod := by
  rw [map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => (map_pow f (y i) (a i)).symm))

theorem exists_level (hL : Laws) {F : Type} [Field F] (Q : PolAV (Sp F)) {g : ℕ} (hg : Q.g = g) {M : ℕ}
    (hM : (M : F) ≠ 0) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M) (x : Fin (2 * g) → (baseOver (Sp F) ⟶ Q.A))
    (hx : ∀ i, x i ^ M = 1) (hp : ∀ i j, WeilIs Q.A Q.L M (x i) (x j) (unitOn ζ ^ stdSymp g i j)) :
    ∃ lev : Out.Level Q M (unitOn ζ), levelBasis lev hg = x := by
  subst hg
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
  refine exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ Q M _
    (hζ.map_of_injective (Units.map_injective inj)) (fun K _ s => ⟨?_, ?_⟩) x hx hp
  · rw [← map_natCast (Spec.preimage s).hom]
    exact (map_ne_zero _).2 hM
  · have : Nontrivial Γ(Spec (CommRingCat.of K), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective.nontrivial
    exact hζ.map_of_injective (Units.map_injective
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).injective)

theorem exists_iso_of_reads (hL : Laws) (hT : ThetaPtDeterminesSt) {F : Type} [Field F] [IsAlgClosed F]
    {B B' : NumB F} {Q Q' : PolAV (Sp F)} (hg : Q'.g = Q.g) {E : B.A ≃* (baseOver (Sp F) ⟶ Q.A)}
    {E' : B'.A ≃* (baseOver (Sp F) ⟶ Q'.A)} (hE : Reads B Q E) (hE' : Reads B' Q' E') {n : ℕ} (hn : n.Prime)
    (ho : Odd n) (hF : (n : F) ≠ 0) : ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : B.A → B'.A), c ≠ 0 →
      TorsMap B B' (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧
        ∀ b, b ^ (n ^ j) ^ 2 = 1 → E b ≫ σ.hom = E' (ρ b) := by
  refine ⟨((n ^ 2) ^ 2) ^ Q.g * Q.g.factorial + 4, fun J hJ c ρ hc hρ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : ((n ^ 2) ^ 2) ^ Q.g * Q.g.factorial < n ^ (j + 4) :=
    lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hm : ((n ^ (j + 4) : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hF
  have hM : (((n ^ (j + 4)) ^ 2 : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hm
  have hM1 : 1 ≤ (n ^ (j + 4)) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hlev := nonempty_level_prime_pow hL F Q n ((j + 4) * 2) hn hF
  rw [pow_mul] at hlev
  have hT' := hT Q.g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) hB F hF Q Q' rfl hg
  have hom : Odd (n ^ (j + 4)) := ho.pow
  generalize n ^ (j + 4) = m at *
  have : NeZero ((m ^ 2 : ℕ) : F) := ⟨hM⟩
  have : NeZero (m ^ 2) := ⟨by omega⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective
  obtain ⟨lev⟩ := hlev (unitOn ζ) (hζ.map_of_injective (Units.map_injective inj))
  let T : Subgroup B.A := (powMonoidHom (m ^ 2)).ker
  let f : T →* (baseOver (Sp F) ⟶ Q.A) := E.toMonoidHom.comp T.subtype
  let f' : T →* (baseOver (Sp F) ⟶ Q'.A) :=
    E'.toMonoidHom.comp (MonoidHom.mk' (fun t => ρ t.1) fun s t => (hρ.1 s.1 t.1 s.2 t.2).1)
  let b : Fin (2 * Q.g) → T := fun i => ⟨E.symm (lev.pt i), by
    show E.symm (lev.pt i) ^ m ^ 2 = 1
    rw [← map_pow, lev.torsion, map_one]⟩
  have hb : lev.pt = fun i => f (b i) := funext fun i => (E.apply_symm_apply _).symm
  obtain ⟨lev', hb'⟩ := exists_level hL Q' hg hM hζ (fun i => f' (b i))
    (fun i => by
      show E' (ρ (b i).1) ^ m ^ 2 = 1
      rw [← map_pow, (hρ.2 _ (b i).2).1, map_one])
    (fun i k => by
      have p₁ := hE.1 _ hM1 _ _ (b i).2 (b k).2
      have p₂ := hE'.1 _ hM1 _ _ (hρ.2 _ (b i).2).1 (hρ.2 _ (b k).2).1
      rw [(hρ.1 _ _ (b i).2 (b k).2).2] at p₂
      simp only [b, MulEquiv.apply_symm_apply] at p₁
      rw [← ((hL.weil _ Q (m ^ 2) (baseOver _)).1 _ _ (lev.torsion i) (lev.torsion k)).unique p₁ (lev.pairing i k)]
      exact p₂)
  let t : (Fin (2 * Q.g) → ℕ) → T := fun a => (List.ofFn fun i => b i ^ a i).prod
  have e : ∀ a, linComb lev.pt a = E (t a).1 := fun a => by rw [hb]; exact linComb_map f b a
  have e' : ∀ a, linComb (levelBasis lev' hg) a = E' (ρ (t a).1) := fun a => by rw [hb']; exact linComb_map f' b a
  let u : (Fin (2 * Q.g) → ZMod (m ^ 2)) → B.A := fun a => (t fun i => (a i).val).1
  have hu : ∀ a, u a ^ m ^ 2 = 1 := fun a => (t _).2
  have v₁ := isThetaPt_mul (fnOf c) ((IsUnit.mk0 c hc).map _) (hE.2 m hom hm _ u hu)
  have v₂ := hE'.2 m hom hm _ (fun a => ρ (u a)) fun a => (hρ.2 _ (hu a)).1
  have q : (fun a => fnOf (B'.uth m (ρ (u a)) 1)) = fun a => fnOf c * fnOf (B.uth m (u a) 1) :=
    funext fun a => by rw [(hρ.2 _ (hu a)).2]; exact map_mul _ _ _
  rw [q] at v₂
  have l : levelPoint lev rfl = fun a => E (u a) := funext fun a => e _
  have l' : levelPoint lev' hg = fun a => E' (ρ (u a)) := funext fun a =>
    (ThetaPtDet.levelPoint_eq _ _ _).trans (e' _)
  obtain ⟨σ, hσ, hσb⟩ := hT' _ lev lev' _ (l ▸ v₁) (l' ▸ v₂)
  refine ⟨σ, hσ, fun x hx => ?_⟩
  have := hσ.1
  obtain ⟨d, hd⟩ := lev.span F (𝟙 _) (E x) (by rw [← map_pow, hx, map_one])
  have hd' : linComb lev.pt (fun i => (d i : ℕ)) = E x :=
    (congrArg (linComb · _) (funext fun i => (Category.id_comp (lev.pt i)).symm)).trans hd
  have hx' : x = (t fun i => (d i : ℕ)).1 := E.injective (hd'.symm.trans (e _))
  rw [← hd', ThetaPtDet.linComb_comp, hx', ← e']
  exact congrArg (linComb · _) (funext hσb)

theorem exists_iso_fib : Laws → ThetaPtDeterminesSt → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult → D.P.g = D'.P.g → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ n : ℕ, n.Prime → Odd n → (n : F) ≠ 0 → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : N.A → N'.A), c ≠ 0 → TorsMap N.toNumB N'.toNumB (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧ ∀ (x : baseOver (Sp F) ⟶ Q.A) (b : N.A), b ^ (n ^ j) ^ 2 = 1 → (ν.eA b).left = x.left ≫ Φ → (ν'.eA (ρ b)).left = (x ≫ σ.hom).left ≫ Φ' := by
  intro hL hT hU R _ _ D D' a₁ a₂ a₃ a₄ hg F _ _ _ N N' ν ν' Q Q' Φ Φ' hΦ hΦ' n hn ho hF
  obtain ⟨E, hE, rE⟩ := exists_reads hU a₁ a₂ ν hΦ
  obtain ⟨E', hE', rE'⟩ := exists_reads hU a₃ a₄ ν' hΦ'
  obtain ⟨j₀, h⟩ := exists_iso_of_reads hL hT (hΦ'.2.2.trans (hg.symm.trans hΦ.2.2.symm)) rE rE' hn ho hF
  refine ⟨j₀, fun j hj c ρ hc hρ => ?_⟩
  obtain ⟨σ, hσ, hb⟩ := h j hj c ρ hc hρ
  refine ⟨σ, hσ, fun x b hb' hx => ?_⟩
  obtain rfl : x = E b := Over.OverMorphism.ext
    (hΦ.1.1.hom_ext (hx.symm.trans (hE b)) (by rw [Over.w, Over.w]))
  rw [hb b hb', hE']

end GlobalTheory.Ex.FibIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcIsometryTorsionIntegralGauge
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ArcLift

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {x : K} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ W) :
    x ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

theorem local_noeth {O' : Type} [CommRing O'] [IsDomain O'] {ϖ : O'} (h : GlobalTheory.LN.ArcBase O' ϖ) :
    IsLocalRing O' ∧ IsNoetherianRing O' := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

theorem exists_lift : Laws → BrGtSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] (S : ValuationSubring F), (∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S) → ∃ A : Lift a F, A.ν.Integral S := by
  intro hL hG E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb F _ _ _ S hS
  obtain ⟨_, _⟩ := local_noeth hb
  obtain ⟨N, ν, hν⟩ := _root_.GlobalTheory.ValuesExist.exists_integral_values hL O' a.D₀ a.even a.bimult F S hS
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hrW : H.rt0 ∈ W₀ := mem_of_pow_mem W₀ two_ne_zero (by
    rw [H.sqrt_neg_disc_sq]; exact neg_mem (natCast_mem W₀ _))
  have hzW : zeta l.A ∈ W₀ := mem_of_pow_mem W₀ l.A_pos.ne' (by
    rw [zeta, (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]; exact one_mem _)
  let r : c.V W₀ := ⟨⟨H.rt0, hr⟩, hrW⟩
  let z : c.V W₀ := ⟨⟨zeta l.A, hz⟩, hzW⟩
  obtain ⟨hdet, I, hζ, hA, hM⟩ := a.geom F r z rfl rfl _ rfl
  have hq := fun n (v : D.La) =>
    (((hG O' a.D₀ a.even a.bimult F N ν).2.2.2.2 n).1 (I.ev n v)).exists
  choose q hq using hq
  have hr2 : r ^ 2 = -(H.d : c.V W₀) := by
    apply Subtype.ext; apply Subtype.ext
    simpa [r] using H.sqrt_neg_disc_sq
  refine ⟨{ ρ := algebraMap (FractionRing O') F (algebraMap O' _ (b r))
            ρ_sq := by rw [← map_pow, ← map_pow, ← map_pow, hr2, map_neg, map_neg, map_neg, map_natCast, map_natCast, map_natCast]
            det := fun τ => by
              obtain ⟨n, h1, h2⟩ := hdet τ
              exact ⟨n, h1, by
                rw [h2]
                by_cases h : τ H.rt = algebraMap (FractionRing O') F (algebraMap O' _ (b r))
                · rw [if_pos h]; exact if_pos h
                · rw [if_neg h]; exact if_neg h⟩
            I := I, N := N, ν := ν, q := q, hq := hq
            be := { be := a.be.comp ν.eX.toIntLinearEquiv.toLinearMap ν.eX.toIntLinearEquiv.toLinearMap
                    symm := fun y z => a.be_symm _ _
                    pos := fun y hy => a.be_pos _ (by simpa using hy)
                    dvd := fun y z => a.be_dvd _ _ }
            be_eq := fun _ _ => rfl
            ρ_eq := fun r' h => by
              obtain rfl : r' = r := Subtype.ext (Subtype.ext h)
              rfl
            ζ_eq := fun z' h => by
              obtain rfl : z' = z := Subtype.ext (Subtype.ext h)
              exact hζ
            levA := hA
            levM := hM
            closed := inferInstance }, hν⟩

end GlobalTheory.Ex.ArcLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisRecombinationInvertibleMatrixTrait
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.Recombine
open GlobalTheory.FrameGen

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

theorem exists_lin (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (c : Fin n → Γ(T'.left, ⊤)) : ∃ s, Lin G L N h b c s := by
  choose b' hb' using fun i => exists_pull hL h (b i)
  refine ⟨SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b', fun z J hJ => ?_⟩
  refine (SectionScalarValuation.sval_lin (s := SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b')
    (fun i => (fst T' G).left.appTop.hom (c i)) b' (fun _ => rfl) (𝟙 _) z hJ).trans
    (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_)
  · exact (gs_pull (𝟙 _) (fst T' G).left z ⊤ trivial (c i)).trans (by rw [Category.id_comp])
  · exact (hb' i _ (𝟙 _) z J hJ).trans (by rw [Category.id_comp]; rfl)

section
variable {T T₁ T₂ T₃ : Over Z} {m n l : ℕ} {h₁ : T ⟶ T₁} {a : Fin m → LB.Sec (LPow G L (N : ℤ) T₁)} {h₂ : T ⟶ T₂}
  {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {h₃ : T ⟶ T₃} {c : Fin l → LB.Sec (LPow G L (N : ℤ) T₃)}

theorem rel_id_iff (hL : L.IsLB) {a : Fin m → LB.Sec (LPow G L (N : ℤ) T)} {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)} :
    Rel G L N (𝟙 _) a h₂ b M ↔ ∀ k, Lin G L N h₂ b (M k) (a k) := by
  constructor
  · intro H k z J hJ
    have := H k _ (𝟙 _) z J hJ
    simp only [Category.id_comp, ← gs_top, id_whiskerRight, Over.id_left] at this
    exact this
  · intro H k Y r z J hJ
    rw [id_whiskerRight, Over.id_left, Category.comp_id]
    exact lin_all hL (H k) r z hJ

theorem rel_inv {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)} {V : Matrix (Fin n) (Fin m) Γ(T.left, ⊤)}
    (H : Rel G L N h₁ a h₂ b M) (e : V * M = (1 : Matrix (Fin n) (Fin n) Γ(T.left, ⊤))) : Rel G L N h₂ b h₁ a V := by
  intro k Y r z J hJ
  rw [Rel.refl (h₁ := h₂) (a := b) k Y r z J hJ, ← e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [H _ Y r z J hJ, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem basisAlong_of_rel (hL : L.IsLB) {a : Fin n → LB.Sec (LPow G L (N : ℤ) T₁)} {M V : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)}
    (hb : BasisAlong G L N h₂ b)
    (H : Rel G L N h₁ a h₂ b M) (e : V * M = 1) (e' : M * V = 1) : BasisAlong G L N h₁ a := by
  intro s
  obtain ⟨P, hP⟩ := exists_rel hL hb (𝟙 _) (fun _ : Fin 1 => s)
  have key : ∀ c, Lin G L N h₁ a c s → Matrix.of (fun _ : Fin 1 => c) = P * V := fun c hc => by
    have r : Rel G L N (𝟙 _) (fun _ : Fin 1 => s) h₁ a (Matrix.of fun _ : Fin 1 => c) := (rel_id_iff hL).2 fun _ => hc
    rw [hP.unique hL hb (r.trans H), Matrix.mul_assoc, e', Matrix.mul_one]
  exact ⟨(P * V) 0, (rel_id_iff hL).1 (hP.trans (rel_inv H e)) 0, fun c hc => congrFun (key c hc) 0⟩

theorem exists_common (hL : L.IsLB) {b : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)} {M} (H : Rel G L N h₁ a h₃ c M)
    (H' : Rel G L N h₂ b h₃ c M) (k : Fin m) :
    ∃ s, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) s ∧ Lin G L N h₂ (fun _ : Fin 1 => b k) (fun _ => 1) s := by
  obtain ⟨s, hs⟩ := exists_lin hL h₁ (fun _ : Fin 1 => a k) (fun _ => 1)
  refine ⟨s, hs, fun z J hJ => (hs z J hJ).trans ?_⟩
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  have := (H k _ (𝟙 _) z J hJ).trans (H' k _ (𝟙 _) z J hJ).symm
  rw [Category.id_comp, Category.id_comp] at this
  exact congrArg _ this

theorem exists_common_pull (hL : L.IsLB) {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {b' : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)}
    {p : T₁ ⟶ T₃} {P : Matrix (Fin m) (Fin l) Γ(T₁.left, ⊤)} {U : Matrix (Fin m) (Fin n) Γ(T₂.left, ⊤)}
    {B : Matrix (Fin n) (Fin l) Γ(T.left, ⊤)} (r₁ : Rel G L N (𝟙 _) a p c P) (r₂ : Rel G L N (𝟙 _) b' (𝟙 _) b U)
    (r₃ : Rel G L N h₂ b h₃ c B) (e₁ : h₁ ≫ p = h₃) (e₂ : P.map h₁.left.appTop.hom = U.map h₂.left.appTop.hom * B)
    (k : Fin m) :
    ∃ s, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) s ∧ Lin G L N h₂ (fun _ : Fin 1 => b' k) (fun _ => 1) s := by
  have r₄ := r₁.pull h₁
  have r₅ := r₂.pull h₂
  rw [Category.comp_id] at r₄ r₅
  rw [e₁, e₂] at r₄
  exact exists_common hL r₄ (r₅.trans r₃) k

end

abbrev fnHom (R : Type) [CommRing R] : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem map_fnHom {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    (M.map (fnHom R)).map (spMap f).appTop.hom = (M.map f).map (fnHom R') := by
  ext1 i j
  exact (congrArg (fun q => q.hom (M i j)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem exists_rel_id (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) {m n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (M : Matrix (Fin m) (Fin n) Γ(T'.left, ⊤)) : ∃ a, Rel G L N (𝟙 _) a h b M := by
  choose a ha using fun i => exists_lin hL h b (M i)
  exact ⟨a, (rel_id_iff hL).2 ha⟩

theorem map_inv_mul {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {n : ℕ} {U : Matrix (Fin n) (Fin n) R}
    (hU : IsUnit U.det) : U⁻¹.map f * U.map f = 1 ∧ U.map f * U⁻¹.map f = 1 :=
  ⟨Matrix.map_mul.symm.trans (by rw [Matrix.nonsing_inv_mul _ hU, Matrix.map_one _ (map_zero _) (map_one _)]),
    Matrix.map_mul.symm.trans (by rw [Matrix.mul_nonsing_inv _ hU, Matrix.map_one _ (map_zero _) (map_one _)])⟩

theorem map_fnHom_mul {R W F : Type} [CommRing R] [CommRing W] [CommRing F] (f : R →+* F) (g : W →+* F) {n : ℕ}
    {P : Matrix (Fin n) (Fin n) R} {U : Matrix (Fin n) (Fin n) W} {B : Matrix (Fin n) (Fin n) F}
    (e : P.map f = U.map g * B) : (P.map (fnHom R)).map (spMap f).appTop.hom =
      (U.map (fnHom W)).map (spMap g).appTop.hom * B.map (fnHom F) := by
  rw [map_fnHom, map_fnHom, e, Matrix.map_mul]

theorem exists_recombination : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), L.IsLB → ∀ (N : ℕ) (K K₂ : Type) [Field K] [Field K₂] (x : Sp K ⟶ Z) (ie : K →+* K₂) (x₂ : Sp K₂ ⟶ Z), spMap ie ≫ x = x₂ → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (Φ : Matrix (Fin n) (Fin n) K₂), ∃ f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x₂)), ∀ (W : Type) [CommRing W] [IsDomain W] (gam : K₂ →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap (gam.comp ie) ≫ x = jK W ≫ χ) (h₂ : spMap gam ≫ x₂ = jK W ≫ χ) (B : Matrix (Fin n) (Fin n) (FractionRing W)) (U : Matrix (Fin n) (Fin n) W), BasisBy G L N x (gam.comp ie) χ h τ B → IsUnit U.det → Φ.map gam = U.map (algebraMap W (FractionRing W)) * B → FrameAt G L N x₂ gam χ h₂ f := by
  intro Z G L hL N K K₂ _ _ x ie x₂ hx n τ Φ
  obtain ⟨f, r₁⟩ := exists_rel_id hL (Over.homMk (spMap ie) hx : Over.mk x₂ ⟶ Over.mk x) τ (Φ.map (fnHom K₂))
  refine ⟨f, fun W _ _ gam χ h h₂ B U H hU e => ?_⟩
  obtain ⟨b, hb, hB⟩ := H
  obtain ⟨b', r₂⟩ := exists_rel_id hL (𝟙 (Over.mk χ)) b (U.map (fnHom W))
  have r₃ : Rel G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) b
      (Over.homMk (spMap (gam.comp ie)) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) τ (B.map (fnHom (FractionRing W))) :=
    rel_of_lin hL fun k => (hB k).imp fun _ H => H.symm
  exact ⟨b', basisAlong_of_rel hL hb r₂ (map_inv_mul (fnHom W) hU).1 (map_inv_mul (fnHom W) hU).2,
    exists_common_pull hL r₁ r₂ r₃ (Over.OverMorphism.ext (spMap_comp' ie gam).symm) (map_fnHom_mul gam _ e)⟩

end GlobalTheory.Recombine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldCentredAtPrime
section
namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_centred_at_prime :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (P : Ideal R), P.IsPrime → P ≠ ⊥ → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ∀ r ∈ P, ‖gam (algebraMap R K r)‖ < 1 := by
  intro R K _ _ _ _ _ _ _ P hP hP0
  obtain ⟨O, _, _, _, _, φ, hker, hcom⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) P (bot_lt_iff_ne_bot.2 hP0)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, h1, h2⟩ :=
    GlobalTheory.Ex.exists_complete_isAlgClosed_cExt O (FractionRing O)
  let ψ : R →+* C := (algebraMap (FractionRing O) C).comp ((algebraMap O (FractionRing O)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing O) C).injective.comp
      ((IsFractionRing.injective O (FractionRing O)).comp hφ)
  letI : Algebra R C := ψ.toAlgebra
  haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hψ
  let g : K →ₐ[R] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : ∀ r, g.toRingHom (algebraMap R K r) = ψ r := fun r => g.commutes r
  refine ⟨C, i1, i2, i3, i4, g.toRingHom, fun r => ?_, fun r hr => ?_⟩
  · rw [hg]
    exact h1 (φ r)
  · rw [hg]
    exact h2 (φ r) (by rw [← hcom] at hr; exact hr)

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteAlgClosedFieldPowerSeriesExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_powerSeries :
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing O') C) (gam : K →+* C) (u : Cˣ), (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) ∧ (∀ r, ‖gam (algebraMap (PowerSeries O') K r)‖ ≤ 1) ∧ (u : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) ∧ ‖(u : C)‖ < 1 := by
  intro O' _ _ K _ _ _ _
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, hle, hlt⟩ :=
    exists_complete_isAlgClosed_cExt (PowerSeries (FractionRing O'))
      (FractionRing (PowerSeries (FractionRing O')))
  let ψ : PowerSeries (FractionRing O') →+* C :=
    (algebraMap (FractionRing (PowerSeries (FractionRing O'))) C).comp
      (algebraMap (PowerSeries (FractionRing O')) _)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing (PowerSeries (FractionRing O'))) C).injective.comp
      (IsFractionRing.injective (PowerSeries (FractionRing O')) (FractionRing (PowerSeries (FractionRing O'))))
  let φ : PowerSeries O' →+* C := ψ.comp (PowerSeries.map (algebraMap O' (FractionRing O')))
  have hφ : Function.Injective φ :=
    hψ.comp (PowerSeries.map_injective _ (IsFractionRing.injective O' (FractionRing O')))
  let _ : Algebra (PowerSeries O') C := φ.toAlgebra
  have : FaithfulSMul (PowerSeries O') C := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  let g : K →ₐ[PowerSeries O'] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : ∀ r, g.toRingHom (algebraMap (PowerSeries O') K r) = φ r := fun r => g.commutes r
  have hX : φ PowerSeries.X ≠ 0 := fun h =>
    PowerSeries.X_ne_zero (hφ (h.trans (map_zero φ).symm))
  refine ⟨C, i1, i2, i3, i4, (ψ.comp PowerSeries.C).toAlgebra, g.toRingHom, Units.mk0 _ hX,
    fun x => ?_, fun r => ?_, (hg _).symm, ?_⟩
  · rw [hg]
    change ψ (PowerSeries.C _) = ψ (PowerSeries.map _ _)
    rw [PowerSeries.map_C]
  · rw [hg]
    exact hle _
  · change ‖ψ (PowerSeries.map _ PowerSeries.X)‖ < 1
    rw [PowerSeries.map_X]
    refine hlt _ ?_
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTripleStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
theorem _root_.GlobalTheory.T.exists_polAV_generic_fibre_of_triple : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)), PolAt t (jK R) → letI := H.starRing; ∃ (A : PolAV (Sp (FractionRing R))) (oA : A.OAct (𝓞 E)) (gen : (Over.pullback (jK R)).obj t.G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ ∀ x, (Over.pullback (jK R)).map (t.act.act x) ≫ gen.hom = gen.hom ≫ oA.act x := by
  first | exact @GlobalTheory.LN.exists_polAV_of_polAt | exact GlobalTheory.LN.exists_polAV_of_polAt | (intros; apply GlobalTheory.LN.exists_polAV_of_polAt <;> assumption)
end

