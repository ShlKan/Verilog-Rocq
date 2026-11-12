{
  description = "Verilog-Rocq: Verilog semantics in Rocq with desugaring and completeness checking, forked from the Choi/Kim/Kang OOPSLA 2025 artifact";

  inputs = {
    # The ITree specification of RISC-V that this project refines Verilog designs against.
    # It brings its own nixpkgs pin and the versapkgs/stdpp-itree overlays (private BI GitLab).
    # Currently the local checkout, because the extension_refactoring branch is ahead of origin.
    # Once pushed, switch to:
    #   git+ssh://git@gitlab.barkhauseninstitut.org/formula-v/risc-v-itree?ref=extension_refactoring
    risc-v-itree.url = "git+file:///Users/shuanglong.kan/MyProjects/BI/risc-v-itree?ref=extension_refactoring";

    # Follow risc-v-itree's nixpkgs so every Rocq library is the exact version it was built with.
    nixpkgs.follows = "risc-v-itree/nixpkgs";
  };

  outputs = { self, nixpkgs, risc-v-itree }:
    let
      systems = [ "aarch64-darwin" "x86_64-darwin" "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system:
        f (import nixpkgs {
          inherit system;
          overlays = [
            risc-v-itree.overlays.default                     # coqPackages_9_0.risc-v-itree
            risc-v-itree.inputs.versapkgs.overlays.default    # its iris/stdpp/pl-a-la-carte deps
            risc-v-itree.inputs.stdppitree.overlays.default   # stdpp-itree
          ];
        }));
    in
    {
      devShells = forAllSystems (pkgs:
        let cp = pkgs.coqPackages_9_0; in
        {
          default = pkgs.mkShell {
            packages = [
              cp.coq
              cp.stdlib         # Rocq 9 ships the standard library separately
              pkgs.dune_3
              cp.coqutil        # src/Lib/SZ.v uses coqutil.Z.BitOps
              cp.ITree
              cp.paco
              cp.ExtLib
              cp.risc-v-itree   # propagates stdpp, iris, flocq, record-update, stdpp-itree
            ];
            shellHook = ''
              echo "Verilog-Rocq: rocq ${cp.coq.version}, dune ${pkgs.dune_3.version}, ITree ${cp.ITree.version}, risc-v-itree ${cp.risc-v-itree.version}"
            '';
          };
        });
    };
}
