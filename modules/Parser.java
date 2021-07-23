import tlc2.value.IValue;
import tlc2.value.impl.*;

import java.io.*;
import java.util.*;

public class Parser {
  public static IValue parse(final StringValue absolutePath) throws IOException {
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    List<Value> values = new ArrayList<>();
    String line = br.readLine();
    try {
      while (line != null) {
        int x = Integer.parseInt(line);
        values.add(IntValue.gen(x));
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    return new TupleValue(values.toArray(new Value[0]));
  }
}
