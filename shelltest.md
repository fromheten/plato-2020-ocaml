# Platoc examples


```sh
$ echo "(Cmd Print \"yooooo\")" | dune exec bin/platoc.exe -- --stdin
yooooo
```

This should not work!

```sh
$ echo ' (let a-dict-ion {"Hello" 0 \
                          "Good day" 1} \
              cool-getter (lambda d (get d "Hello")) \
              value (cool-getter a-dict-ion))' | dune exec bin/platoc.exe -- --stdin
```
