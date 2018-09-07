files = \
  docs/Mycelium.html \
  docs/Var.html \
  docs/Sub.html \
  docs/Expr.html \
  docs/Type.html \
  docs/Infer.html \
  docs/Jud.html \
  docs/Proof.html \
  docs/Module.html \
  docs/Fancy.html \
  docs/Parser.html \
  docs/Deps.html

docs: $(files) docs/Tests.html docs/Main.html

docs/%.html: src/%.lhs
	pandoc --mathjax -s -c style.css -o $@ $<

docs/Tests.html: test/Tests.lhs
	pandoc --mathjax -s -c style.css -o $@ $<

docs/Main.html: app/Main.lhs
	pandoc --mathjax -s -c style.css -o $@ $<
