minrt.mlの関数間の依存関係解析（どの関数がどの関数を呼び出しているか）

使い方

- test/ に minrt.ml を置く（オリジナルのminrt.mlを使う場合は、最初のtrueとfalseの定義を消さないとparse errorになるので注意）
- トップディレクトリで`make`
	- exception Typing.Error になるが問題ない
	- test/minrt.dotに関数間の依存関係がdot言語で出力される
- test/ で`dot -Tgif minrt.dot -o minrt.gif`
	- dotコマンドは、Macなら`brew install graphviz`でインストールできる
	- test/minrt.gifに関数間の依存関係を表す有向グラフが出力される

test/minrt.ignoreでグラフに表示しない関数を指定しているので、このファイルを変更すれば、グラフに表示する関数を変えられます。  
（このファイルはMakefileに入っていないため、このファイルを変更してから再度makeしても更新されないので気をつけてくださいm(\_ \_)m）
