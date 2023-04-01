# Do With In (base package)

This is an inner package that contains the actual functions and datastructures that form the basis for do-with-in. Do not use it directly. The package do-with-in reexports everything that forms the public interface. Splitting the packages this way was necessary so that do-with-in could reexport both the items from this package and the proc\_macros built using them in the package do-with-in-internal-macros.
