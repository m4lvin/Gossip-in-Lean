
all: gossip

.PHONY: all gossip

gossip: .first-run-done
	lake build Gossip

.first-run-done:
	lake exe cache get
	touch .first-run-done

doc:
	cd docbuild && lake -Kenv=dev build Gossip:docs

show-doc: doc
	(sleep 2 && firefox http://127.0.0.1:8000/Gossip/Basic.html) &
	cd docbuild/.lake/build/doc && python -m http.server --bind 127.0.0.1
