module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CoboundaryFirstSubsetSelmerFirst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelmerSecondClosedUnderLimits
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.LcOfAdic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AutDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa
open scoped TensorProduct

noncomputable section

private theorem gdet_comap_comap {n : ℕ} {A G G' G'' : Type} [CommRing A] [Group G] [Group G'] [Group G'']
    (D : GDet n A G'') (f : G →* G') (f' : G' →* G'') : (D.comap f').comap f = D.comap (f'.comp f) := by
  apply GDet.ext
  intro B _ _ x
  show (D.D B) ((MonoidAlgebra.mapDomainRingHom B f') ((MonoidAlgebra.mapDomainRingHom B f) x)) =
    (D.D B) (MonoidAlgebra.mapDomainRingHom B (f'.comp f) x)
  rw [MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

private theorem mapDom_single {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (a : G) (c : A) :
    MonoidAlgebra.mapDomainRingHom A f (MonoidAlgebra.single a c) = MonoidAlgebra.single (f a) c := by
  simp

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 G0' G G' : Glob l L} {n : ℕ} {O : Type} [CommRing O] [IsLocalRing O]
  [Algebra ℤ_[l] O] {r : Resid G0.frame O n} {r' : Resid G0'.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B]
  {u : Pair r B} {u' : Pair r' B} {J : Ideal B} {σ : Type} {D : ℕ}

@[reducible] private def baseDesc (b : TWBase u J σ D) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ) : TWBase u' J σ D where
  wt := b.wt
  wt_res k := by rw [← hr]; exact b.wt_res k
  lam := b.lam
  segmentWeightExponent k := by rw [hψ]; exact b.segmentWeightExponent k
  M := b.M
  smul_lam := b.smul_lam
  free := b.free
  fin := b.fin
  supp := b.supp

variable {b : TWBase u J σ D} {h : G.Hom G0} {h' : G'.Hom G0'} {q : ℕ} {ut : Fin q → Fin n → O} {N : ℕ}

@[reducible] private def ringDesc (A : TWRing b h ut N) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ)
    (rN' : Resid G'.frame O n) (hc : Glob.Compat h' rN' r') (p' : Pair rN' A.R) (hp : p'.ψ = A.p.ψ) :
    TWRing (baseDesc b hr hψ) h' ut N where
  rN := rN'
  compat := hc
  R := A.R
  p := p'
  s := A.s
  s_w k := by rw [hp]; exact A.s_w k
  U := A.U
  U_res := A.U_res
  M := A.M
  a := A.a
  le_a := A.le_a
  rk := A.rk
  e := A.e
  e_smul := A.e_smul

private def MapsP (A : TWRing b h ut N) (Nq : Fin q → ℕ) (P : Fin q → Polynomial B) : Prop :=
  ∃ (θ : A.R →ₐ[O] Sp P fun j i => algebraMap O B (ut j i))
    (φ : (Sp P fun j i => algebraMap O B (ut j i)) ⊗[B] b.M →+ A.X)
    (ψ : A.X →+ (Sp P fun j i => algebraMap O B (ut j i)) ⊗[B] b.M),
    (A.p.Maps θ.toRingHom ((u.D.comap h.p₀).map (algebraMap B _)) fun v i => pushCh (algebraMap B _) (u.ψ v i)) ∧
    (∀ z, θ (A.s z) = algebraMap B _ (b.lam (MvPowerSeries.constantCoeff z))) ∧
    (∀ j i, θ (A.U j i) = Sp.u _ _ j i) ∧
    (∀ (t : A.R) z, φ (θ t • z) = t • φ z) ∧ (∀ (t : A.R) z, ψ (t • z) = θ t • ψ z) ∧
    (∀ z, φ (ψ z) = fEl Nq A.U • z) ∧ ∀ z, ψ (φ z) = θ (fEl Nq A.U) • z

private theorem maps_desc (A : TWRing b h ut N) (hr : r.psib = r'.psib) (hψ : u'.ψ = u.ψ)
    (rN' : Resid G'.frame O n) (hc : Glob.Compat h' rN' r') (p' : Pair rN' A.R) (hp : p'.ψ = A.p.ψ)
    (g0 : G0.Hom G0') (g : G.Hom G') (comm : ∀ a, h'.p₀ (g.p₀ a) = g0.p₀ (h.p₀ a))
    (hD : u'.D.comap g0.p₀ = u.D) (hpD : p'.D.comap g.p₀ = A.p.D)
    (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (m : TWMaps Nq ph ta A ex) :
    Nonempty (TWMaps Nq (fun j => g.p₀ (ph j)) (fun j => g.p₀ (ta j)) (ringDesc A hr hψ rN' hc p' hp) ex) := by
  have H : MapsP A Nq fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1) :=
    ⟨m.θ, m.φ, m.ψ, m.θ_pair, m.theta_coefficientMap_eq, m.θ_U, m.φ_smul, m.ψ_smul, m.φψ, m.ψφ⟩
  have e : (fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) =
      fun j => u'.D.chi (MonoidAlgebra.single (h'.p₀ (g.p₀ (ph j))) 1) := funext fun j => by
    rw [← hD, (comap_lam n B _ _ g0.p₀ u'.D).1, mapDom_single, comm]
  rw [e] at H
  obtain ⟨θ, φ, ψ, ⟨h1, h1'⟩, h2, h3, h4, h5, h6, h7⟩ := H
  have htr : ∀ y, p'.D.tr (MonoidAlgebra.mapDomainRingHom A.R g.p₀ y) = A.p.D.tr y := fun y => by
    rw [← hpD, (comap_lam n A.R _ _ g.p₀ p'.D).2.2.1]
  obtain ⟨-, -, s1, s2⟩ := map_star l L G G' g n O A.R
  refine ⟨⟨θ, ⟨?_, fun v i => ?_⟩, h2, h3, φ, ψ, h4, h5, h6, h7, fun j a x => ?_, fun j i a x => ?_⟩⟩
  · refine ((comap_lam n _ _ _ g.p₀ _).2.2.2.2.2 g.p₀_surj).1 _ ?_
    have e1 := (comap_lam n _ _ _ g.p₀ p'.D).2.2.2.1 _ θ.toRingHom
    have e2 := (comap_lam n _ _ _ g.p₀ (u'.D.comap h'.p₀)).2.2.2.1 _
      (algebraMap B (SpAt u' (fun j => h'.p₀ (g.p₀ (ph j))) ut))
    have e3 : (u'.D.comap h'.p₀).comap g.p₀ = u.D.comap h.p₀ := by
      rw [← hD, gdet_comap_comap, gdet_comap_comap]
      exact congrArg _ (MonoidHom.ext comm)
    rw [hpD] at e1
    rw [e3] at e2
    exact e1.symm.trans (h1.trans e2)
  · have := h1' v i
    rw [← hp, ← hψ] at this
    exact this
  · obtain ⟨a, rfl⟩ := g.p₀_surj a
    have := m.rel1 j a x
    rw [← htr, map_mul, mapDom_single, s1] at this
    exact this
  · obtain ⟨a, rfl⟩ := g.p₀_surj a
    have := m.rel2 j i a x
    rw [← htr, map_mul, mapDom_single, s2] at this
    exact this

end

private theorem apply_mem_openNormalSubgroup_of_mem_PL_comap (l : ℕ) {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ']
    [TopologicalSpace Γ'] (f : Γ →* Γ') (hf : Continuous f) (H : OpenNormalSubgroup Γ') (a : Γ)
    (ha : a ∈ PL l (Subgroup.comap f (H.toOpenSubgroup : Subgroup Γ'))) :
    f a ∈ (H.toOpenSubgroup : Subgroup Γ') := by
  let U : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨(H.toOpenSubgroup : Subgroup Γ').comap f, H.isOpen'.preimage hf⟩
      isNormal' := Subgroup.Normal.comap H.isNormal' f }
  have hU : PL l (Subgroup.comap f (H.toOpenSubgroup : Subgroup Γ')) ≤ (U.toOpenSubgroup : Subgroup Γ) :=
    iInf_le_of_le U (iInf_le_of_le (fun k hk => ⟨0, by rw [pow_zero, pow_one]; exact hk⟩) le_rfl)
  exact hU ha

theorem UpperTheory.V.Pa.aut_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (r' : Resid Q.G0'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (u' : Pair r' B) (J : Ideal B) (σ : Type) (D : ℕ), Adapted T (r := r) → Glob.Compat Q.g0 r r' → u'.D.comap Q.g0.p₀ = u.D → u'.ψ = u.ψ → TWAut u J σ D T → Nonempty (TWAut u' J σ D Q.grp) := by
  intro l _ L G0 T Q n O _ _ _ _ _ r r' B _ _ _ u u' J σ D hAd hC hD hψ W
  have hr : r.psib = r'.psib := hC.2.1
  have key : ∀ N : ℕ, ∃ (rN' : Resid (Q.GN' N).frame O n) (_ : Glob.Compat (Q.h' N) rN' r')
      (p' : Pair rN' (W.A N).R) (_ : p'.ψ = (W.A N).p.ψ), p'.D.comap (Q.gN N).p₀ = (W.A N).p.D := by
    intro N
    have hchi : ∀ (a : (T.GN N).G₀) (i : Fin n), (W.A N).rN.chib i a = r.chib i ((T.h N).p₀ a) :=
      fun a i => by rw [(W.A N).compat.1 i]; rfl
    have hH : ∀ a : (T.GN N).G₀,
        (a : (T.GN N).Γ) ∈ Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ) →
        ∀ i, (W.A N).rN.chib i a = 1 := by
      intro a ha i
      rw [hchi]
      exact hAd.1 ((T.h N).p₀ a) ha i
    obtain ⟨rN', hc1, _⟩ := resid_desc l L (T.GN N) (Q.GN' N) (Q.gN N) n O (W.A N).rN (by
      intro a ha i
      apply hH a _ i
      have hk : (a : (T.GN N).Γ) ∈ (Q.gN N).p.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val ha
      rw [Q.kerN N] at hk
      exact apply_mem_openNormalSubgroup_of_mem_PL_comap l (T.h N).p (T.h N).cont T.H _ hk)
    have hleη : Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ) ≤ (T.GN N).η.ker := by
      intro a ha
      rw [MonoidHom.mem_ker, ← (T.h N).η a]
      exact T.H_η _ ha
    obtain ⟨p', hpD, hp⟩ := pair_desc l L (T.GN N) (Q.GN' N) (Q.gN N) n O (W.A N).rN rN' (W.A N).R (W.A N).p
      (Subgroup.comap (T.h N).p (T.H.toOpenSubgroup : Subgroup G0.Γ))
      (T.H.isOpen'.preimage (T.h N).cont) hleη hH (Q.kerN N) hc1
    refine ⟨rN', ⟨fun i => ?_, ?_, ?_⟩, p', hp, hpD⟩
    · refine MonoidHom.ext fun b => ?_
      obtain ⟨a, rfl⟩ := (Q.gN N).p₀_surj b
      show rN'.chib i ((Q.gN N).p₀ a) = r'.chib i ((Q.h' N).p₀ ((Q.gN N).p₀ a))
      rw [Q.comm₀ N a]
      have e1 : (W.A N).rN.chib i a = rN'.chib i ((Q.gN N).p₀ a) := by rw [hc1.1 i]; rfl
      have e2 : r.chib i ((T.h N).p₀ a) = r'.chib i (Q.g0.p₀ ((T.h N).p₀ a)) := by rw [hC.1 i]; rfl
      rw [← e1, hchi, e2]
    · exact hc1.2.1.symm.trans ((W.A N).compat.2.1.trans hr)
    · exact hc1.2.2.symm.trans ((W.A N).compat.2.2.trans hC.2.2)
  choose rN' hc p' hp hpD using key
  refine ⟨⟨baseDesc W.b hr hψ, W.ut, ?_, fun N => ringDesc (W.A N) hr hψ (rN' N) (hc N) (p' N) (hp N),
    W.ex, fun N => ?_⟩⟩
  · intro j i
    rw [W.ut_res j i, hC.1 i]
    rfl
  · exact (maps_desc (W.A N) hr hψ (rN' N) (hc N) (p' N) (hp N) Q.g0 (Q.gN N) (Q.comm₀ N) hD (hpD N)
      (T.Nq N) (T.ph N) (T.ta N) W.ex (W.m N)).some
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.BDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G0 G0' : Glob l L} (g : G.Hom G') (h : G.Hom G0) (g0 : G0.Hom G0')
  (h' : G'.Hom G0') (hc : ∀ a, h'.p₀ (g.p₀ a) = g0.p₀ (h.p₀ a)) {n : ℕ} {x : NP G0.frame n} (k : Kap x)
  (ρ' : G0'.G₀ →* GL (Fin n) x.A) (hρ : ∀ a, ρ' (g0.p₀ a) = x.ρ a)
  (κ' : Fin k.g → G0'.G₀ → Matrix (Fin n) (Fin n) x.A) (hκ : ∀ j a, κ' j (g0.p₀ a) = k.κ j a)
  (X : Type) [CommRing X] [Algebra x.A X]

private theorem pull_inj {Z : Type} : Function.Injective fun (z : G'.G₀ → Z) (a : G.G₀) => z (g.p₀ a) :=
  fun _ _ e => funext fun b => by
    obtain ⟨a, rfl⟩ := g.p₀_surj b
    exact congrFun e a

include hc

private theorem rhoX_eq : (fun a => (x.desc g0 ρ' hρ).ρX X (h'.p₀ (g.p₀ a))) = fun a => x.ρX X (h.p₀ a) :=
  funext fun a => by rw [hc, NP.desc_ρX]

private theorem first_order_lift_comp_pullback :
    (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ (g.p₀ a))) = fun a => k.ρ1 X (h.p₀ a) :=
  funext fun a => by
    rw [hc]
    show (1 + DD.epM fun j => (κ' j (g0.p₀ (h.p₀ a))).map (algebraMap x.A X)) *
      (x.desc g0 ρ' hρ).ρX (DD X k.g) (g0.p₀ (h.p₀ a)) = _
    rw [NP.desc_ρX]
    simp only [hκ]
    rfl

private theorem selP_iff (z : G'.G₀ → Matrix (Fin n) (Fin n) X) :
    (fun a => z (g.p₀ a)) ∈ SelP h x X ↔ z ∈ SelP h' (x.desc g0 ρ' hρ) X := by
  have := g.sel_iff x.t (fun a => (x.desc g0 ρ' hρ).ρX X (h'.p₀ a)) (x.wX X) (x.wiX X) (Ev x.A X n x.a) z
  rw [rhoX_eq g h g0 h' hc ρ' hρ X] at this
  exact this

private theorem mem_selmer_first_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Sel1 h X k ↔ z ∈ Sel1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.sel_iff x.t (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (k.w1 X) (k.wi1 X) (W1 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem mem_selmer_second_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Sel2 h X k ↔ z ∈ Sel2 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.sel_iff x.t (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (k.w1 X) (k.wi1 X) (W2 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem mem_coboundary_first_iff_pullback (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (fun a => z (g.p₀ a)) ∈ Bd1 h X k ↔ z ∈ Bd1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  have := g.bd_iff (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) (W1 n x.A X k.g x.a) z
  rw [first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X] at this
  exact this

private theorem coboundary_first_eq_image_pullback :
    Bd1 h X k = (fun (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) (a : G.G₀) => z (g.p₀ a)) ''
      Bd1 h' X (k.desc g0 ρ' hρ κ' hκ) := by
  ext z
  constructor
  · intro hz
    obtain ⟨Y, -, -, e⟩ := id hz
    have e' : z = fun a => dY G'.frame (fun a => (k.desc g0 ρ' hρ κ' hκ).ρ1 X (h'.p₀ a)) Y (g.p₀ a) := by
      funext a
      rw [e, ← g.dY_comp, first_order_lift_comp_pullback g h g0 h' hc k ρ' hρ κ' hκ X]
    refine ⟨_, (mem_coboundary_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).1 (e' ▸ hz), e'.symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact (mem_coboundary_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).2 hz

private theorem pullback_selmer_first_subset :
    (fun (z : G'.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) (a : G.G₀) => z (g.p₀ a)) ''
      Sel1 h' X (k.desc g0 ρ' hρ κ' hκ) ⊆ Sel1 h X k := by
  rintro _ ⟨z, hz, rfl⟩
  exact (mem_selmer_first_iff_pullback g h g0 h' hc k ρ' hρ κ' hκ X _).2 hz

end

theorem UpperTheory.V.Pa.b_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Q : TWQuot T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (ρ' : Q.G0'.G₀ →* GL (Fin n) x.A) (hρ : ∀ a, ρ' (Q.g0.p₀ a) = x.ρ a) (κ' : Fin k.g → Q.G0'.G₀ → Matrix (Fin n) (Fin n) x.A) (hκ : ∀ j a, κ' j (Q.g0.p₀ a) = k.κ j a) (D0 : ℕ), x.UnipOn T.H.toSubgroup → (T.B1 k D0 → Q.grp.B1 (k.desc Q.g0 ρ' hρ κ' hκ) D0) ∧ (T.B2 k → Q.grp.B2 (k.desc Q.g0 ρ' hρ κ' hκ)) := by
  intro l _ L G0 T Q n x k ρ' hρ κ' hκ D0 hu
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun m => (hC m).mono fun N hN => ?_⟩
    obtain ⟨hf, hle⟩ := hN
    have hs := pullback_selmer_first_subset (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m)
    have hb := coboundary_first_eq_image_pullback (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m)
    refine ⟨(hf.subset hs).of_finite_image (pull_inj (Q.gN N)).injOn, ?_⟩
    have h1 := Set.ncard_le_ncard hs hf
    rw [Set.ncard_image_of_injective _ (pull_inj (Q.gN N))] at h1
    rw [hb, Set.ncard_image_of_injective _ (pull_inj (Q.gN N))] at hle
    exact h1.trans hle
  · rintro ⟨C, hC⟩
    refine ⟨C, fun m => (hC m).mono fun N hN z hz => ?_⟩
    obtain ⟨c, hc, Ψ, hΨ, e⟩ := hN (fun i j a => z i j ((Q.gN N).p₀ a)) fun i j =>
      (selP_iff (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) ρ' hρ (x.Am m) _).2 (hz i j)
    haveI : T.H.toSubgroup.Normal := T.H.isNormal'
    obtain ⟨Ψ', rfl⟩ := (sel_desc l L (T.GN N) (Q.GN' N) G0 (Q.gN N) (T.h N) n x k T.H.toSubgroup m T.H.isOpen'
      (fun a ha => T.H_η a ha) hu (Q.kerN N)).2 Ψ (Or.inr hΨ)
    refine ⟨c, hc, Ψ', (mem_selmer_second_iff_pullback (Q.gN N) (T.h N) Q.g0 (Q.h' N) (Q.comm₀ N) k ρ' hρ κ' hκ (x.Am m) _).1 hΨ,
      fun j γ a b => ?_⟩
    obtain ⟨γ, rfl⟩ := (Q.gN N).p₀_surj γ
    exact e j γ a b
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.FirstCohomologyBoundOfBoundaryBound
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem card_submodule_mul_quotient_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (S B : Submodule A M)
    (hBS : (B : Set M) ⊆ S) (hS : (S : Set M).Finite) (I : Ideal A) (e : ℕ) (φ : (Fin e → A) → M)
    (hφ : ∀ c, φ c ∈ S) (hsub : ∀ c c', φ (c - c') = φ c - φ c') (hI : ∀ c, φ c ∈ B → ∀ i, c i ∈ I) :
    (B : Set M).ncard * Nat.card (A ⧸ I) ^ e ≤ (S : Set M).ncard := by
  haveI : Finite (S : Set M) := hS
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  let f : ↥(B : Set M) × (Fin e → A ⧸ I) → ↥(S : Set M) := fun p =>
    ⟨φ (fun i => s (p.2 i)) + p.1, S.add_mem (hφ _) (hBS p.1.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hh
    have h1 : φ (fun i => s (c i)) + b = φ (fun i => s (c' i)) + b' := congrArg Subtype.val hh
    have h2 : φ ((fun i => s (c i)) - fun i => s (c' i)) ∈ B := by
      rw [hsub]
      have : φ (fun i => s (c i)) - φ (fun i => s (c' i)) = (b' : M) - b := by
        rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
      rw [this]
      exact B.sub_mem b'.2 b.2
    have h3 : c = c' := by
      funext i
      rw [← hs (c i), ← hs (c' i)]
      exact Ideal.Quotient.eq.2 (hI _ h2 i)
    subst h3
    exact Prod.ext (Subtype.ext (add_left_cancel h1)) rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq] at this

theorem UpperTheory.V.Pa.firstCohomologyBound_of_boundaryBound :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (D0 : ℕ), TopFG G.Γ → FirstSelmerCardBoundAtAllLevels h k D0 → K1 h k D0 := by
  intro l _ L G G0 h n x k D0 hfg hB e z hz hind
  obtain ⟨C, hC⟩ := coefficients_bounded_of_selmer_boundary l L G G0 h n x k e z hfg hz hind
  obtain ⟨C', hC'⟩ := hB
  obtain ⟨⟨S0, hS0⟩, -⟩ := sel_lin l G.frame n x.A (DD x.A k.g) x.t (fun g => k.ρ1 x.A (h.p₀ g)) (k.w1 x.A)
    (k.wi1 x.A) (W1 n x.A x.A k.g x.a)
  have hS0' : (S0 : Set _) = Sel1 h x.A k := hS0
  have key : ∀ m, (m - C) * e ≤ m * D0 + C' := by
    intro m
    obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := sel_lin l G.frame n x.A (DD (x.Am m) k.g) x.t (fun g => k.ρ1 (x.Am m) (h.p₀ g))
      (k.w1 (x.Am m)) (k.wi1 (x.Am m)) (W1 n x.A (x.Am m) k.g x.a)
    have hS' : (S : Set _) = Sel1 h (x.Am m) k := hS
    have hB' : (B : Set _) = Bd1 h (x.Am m) k := hB
    obtain ⟨hfin, hle⟩ := hC' m
    have hBS := coboundary_first_subset_selmer_first l L G G0 h n x k (x.Am m)
    rw [← hS'] at hfin hle hBS
    rw [← hB'] at hle hBS
    have hc := card_submodule_mul_quotient_le S B hBS hfin (Ideal.span {x.t ^ (m - C)}) e
      (fun c g => ((∑ i, c i • z i) g).map (x.redD k.g m))
      (fun c => by
        have h1 : (∑ i, c i • z i) ∈ Sel1 h x.A k := by
          rw [← hS0']
          exact S0.sum_mem fun i _ => S0.smul_mem _ (by rw [← SetLike.mem_coe, hS0']; exact hz i)
        have h2 := (sel_red l L G G0 h n x k x.A (x.Am m) (Ideal.Quotient.mkₐ x.A _)).2.1 _ h1
        rw [← hS'] at h2
        exact h2)
      (fun c c' => by
        funext g
        ext1 a b
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.map_apply, Matrix.sub_apply, map_sub])
      (fun c hc => hC m c (by rw [← hB']; exact hc))
    have hcard : Nat.card (x.A ⧸ Ideal.span {x.t ^ (m - C)}) = Nat.card x.K ^ (m - C) :=
      (am_fin l G0.frame n x (m - C) 0).2.1
    have hpos : 0 < Set.ncard (SetLike.coe B) := (Set.ncard_pos (hfin.subset hBS)).2 ⟨0, B.zero_mem⟩
    rw [hcard, ← pow_mul] at hc
    have h3 := Nat.le_of_mul_le_mul_left (hc.trans hle) hpos
    exact (Nat.pow_le_pow_iff_right (am_fin l G0.frame n x 0 0).2.2.2.2.2).1 h3
  by_contra hlt
  have h1 : D0 + 1 ≤ e := by omega
  have h2 := key (C + (C * D0 + C' + 1))
  rw [Nat.add_sub_cancel_left] at h2
  have h3 := (Nat.mul_le_mul_left (C * D0 + C' + 1) h1).trans h2
  nlinarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelmerSecondExistsUltrafilterLimit
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem diag_mk {K : Type} [Field K] (a : ℕ → PowerSeries K) (b : PowerSeries K) (j : ℕ)
    (H : ∀ c < j, Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (c + 1)}) b =
      Ideal.Quotient.mk _ (a c)) :
    Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ j})
      (PowerSeries.mk fun c => PowerSeries.coeff c (a c)) = Ideal.Quotient.mk _ b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro c hc
  have := H c hc
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at this
  have := this c (Nat.lt_succ_self c)
  rw [map_sub, sub_eq_zero] at this ⊢
  rw [PowerSeries.coeff_mk, this]

private theorem lc_of_nil {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (t : R) (ht : IsNilpotent t) (f : Γ → R)
    (hf : AdicCont (Ideal.span {t}) f) : IsLocallyConstant f := by
  obtain ⟨N, hN⟩ := ht
  have h1 : IsLocallyConstant fun g => Ideal.Quotient.mk (Ideal.span {t} ^ N) (f g) := hf N
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk (Ideal.span {t} ^ N)) h1 ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot]

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (hf : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have : ∀ᶠ g in nhds y, ∀ i j, f g i j = f y i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hf i j).eventually_eq y
  exact this.mono fun g hg => Matrix.ext hg

private theorem selmer_second_finite_modulo_power (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n)
    (k : Kap x) (hG : TopFG G.Γ) (j : ℕ) : (Sel2 h (x.Am j) k).Finite := by
  obtain ⟨hfin, -, hn, hn', -⟩ := am_fin l G0.frame n x j k.g
  obtain ⟨-, ⟨h1, hm, -⟩, hlc, -⟩ := rho_hom l G0.frame n x k (x.Am j)
  have hfg : TopFG G.G₀ := (TopFG.subgroup_quot G.Γ hG).1 G.η.ker G.η_open
  have := coc_fin G.G₀ (DD (x.Am j) k.g) n (fun g => k.ρ1 (x.Am j) (h.p₀ g)) hfg
    (by simp only [map_one]; exact h1) (fun g g' => by simp only [map_mul]; exact hm _ _)
    ((hlc hn).2.comp_continuous h.p₀_cont)
  refine this.subset ?_
  rintro z ⟨-, h2, h3, -⟩
  exact ⟨lc_mat z fun a b => lc_of_nil _ hn' _ (h2 a b), h3⟩

theorem UpperTheory.V.Pa.selmer_second_exists_ultrafilter_limit :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (U : Ultrafilter ℕ) (z : ℕ → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), TopFG G.Γ → (U : Filter ℕ) ≤ atTop → (∀ m, (fun g => (z m g).map (x.redD k.g m)) ∈ Sel2 h (x.Am m) k) → ∃ Ψ ∈ Sel2 h x.A k, ∀ j, ∀ᶠ m in (U : Filter ℕ), ∀ g, (Ψ g).map (x.redD k.g j) = (z m g).map (x.redD k.g j) := by
  intro l _ L G G0 h n x k U z hG hU hz
  have hred : ∀ j, ∀ᶠ m in (U : Filter ℕ), (fun g => (z m g).map (x.redD k.g j)) ∈ Sel2 h (x.Am j) k := by
    intro j
    refine ((eventually_ge_atTop j).filter_mono hU).mono fun m hm => ?_
    have hle : Ideal.span {x.t ^ m} ≤ Ideal.span {x.t ^ j} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hm)
    exact (sel_red l L G G0 h n x k (x.Am m) (x.Am j) (Ideal.Quotient.factorₐ x.A hle)).2.2.1 _ (hz m)
  have hst : ∀ j, ∃ m', ∀ᶠ m in (U : Filter ℕ),
      (fun g => (z m g).map (x.redD k.g j)) = fun g => (z m' g).map (x.redD k.g j) := by
    intro j
    obtain ⟨w, ⟨-, hw⟩, -⟩ := ultra_fin ℕ _ U (fun m g => (z m g).map (x.redD k.g j)) _
      (selmer_second_finite_modulo_power l L G G0 h n x k hG j) (hred j)
    obtain ⟨m', hm'⟩ := hw.exists
    exact ⟨m', hw.mono fun m hm => hm.trans hm'.symm⟩
  choose μ hμ using hst
  let Ψ : G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g) := fun g => Matrix.of fun a b =>
    ⟨PowerSeries.mk fun c => PowerSeries.coeff c (z (μ (c + 1)) g a b).a,
     fun i => PowerSeries.mk fun c => PowerSeries.coeff c ((z (μ (c + 1)) g a b).ep i),
     fun i => PowerSeries.mk fun c => PowerSeries.coeff c ((z (μ (c + 1)) g a b).ep' i),
     PowerSeries.mk fun c => PowerSeries.coeff c (z (μ (c + 1)) g a b).eta⟩
  have hΨ : ∀ j, ∀ᶠ m in (U : Filter ℕ), ∀ g, (Ψ g).map (x.redD k.g j) = (z m g).map (x.redD k.g j) := by
    intro j
    have h1 : ∀ᶠ m in (U : Filter ℕ), ∀ c ∈ Finset.range j,
        (fun g => (z m g).map (x.redD k.g (c + 1))) = fun g => (z (μ (c + 1)) g).map (x.redD k.g (c + 1)) :=
      (Filter.eventually_all_finset _).2 fun c _ => hμ (c + 1)
    refine h1.mono fun m hm g => Matrix.ext fun a b => ?_
    have h2 : ∀ c < j, x.redD k.g (c + 1) (z m g a b) = x.redD k.g (c + 1) (z (μ (c + 1)) g a b) := fun c hc =>
      congrFun (congrFun (congrFun (hm c (Finset.mem_range.2 hc)) g) a) b
    refine DD.ext ?_ (funext fun i => ?_) (funext fun i => ?_) ?_
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).a) _ j fun c hc => congrArg DD.a (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).ep i) _ j fun c hc => congrArg (DD.ep · i) (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).ep' i) _ j fun c hc => congrArg (DD.ep' · i) (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).eta) _ j fun c hc => congrArg DD.eta (h2 c hc)
  refine ⟨Ψ, selmer_second_closed_under_limits l L G G0 h n x k Ψ fun j => ?_, hΨ⟩
  obtain ⟨m, hm1, hm2⟩ := ((hΨ j).and (hred j)).exists
  rw [funext hm1]
  exact hm2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TaylorWilesSecondConditionAtLimitOfGroupConditio
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.taylorWiles_second_condition_at_limit_of_group_condition :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x), T.B2 k → SecondSelmerSpanBoundAtAllLevels Λ.h k := by
  intro l _ L G0 T Λ n x k hB
  obtain ⟨C, hC⟩ := hB
  refine ⟨C, fun m z hz => ?_⟩
  obtain ⟨hfin, -, hn1, hn2, -, -⟩ := am_fin l G0.frame n x m k.g
  obtain ⟨⟨a1, a2, -⟩, ⟨b1, b2, -⟩, hlc, -⟩ := rho_hom l G0.frame n x k (x.Am m)
  obtain ⟨c1, c2⟩ := hlc hn1
  have E1 := t1 l L G0 T Λ n x.A (x.Am m) x.t (x.ρX (x.Am m)) (x.wX (x.Am m)) (x.wiX (x.Am m))
    (Ev x.A (x.Am m) n x.a) hn1 a1 a2 c1
  have E2 := t1 l L G0 T Λ n x.A (DD (x.Am m) k.g) x.t (k.ρ1 (x.Am m)) (k.w1 (x.Am m)) (k.wi1 (x.Am m))
    (W2 n x.A (x.Am m) k.g x.a) hn2 b1 b2 c2
  obtain ⟨N, ⟨⟨-, h1, -⟩, ⟨-, -, h2⟩⟩, h3⟩ := ((E1.and E2).and ((hC m).filter_mono Λ.U_le)).exists
  choose zN hzN hrel using fun i j => h1 (z i j) (hz i j)
  obtain ⟨c, hc, ΨN, hΨN, hΨ⟩ := h3 zN hzN
  obtain ⟨Ψ, hΨm, hr⟩ := h2 ΨN hΨN
  refine ⟨c, hc, Ψ, hΨm, fun j γ a b => ?_⟩
  obtain ⟨g, rfl⟩ := Λ.πo0_surj γ
  rw [← hr g, hΨ]
  simp only [hrel _ _ g]
end

