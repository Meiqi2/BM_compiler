package sutd.compiler.simp.web

import com.sun.net.httpserver.{HttpExchange, HttpHandler, HttpServer}
import java.net.InetSocketAddress
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import sutd.compiler.simp.Main

object WebServer {

  private def respond(ex: HttpExchange, code: Int, contentType: String, bytes: Array[Byte]): Unit = {
    ex.getResponseHeaders.add("Content-Type", contentType)
    ex.sendResponseHeaders(code, bytes.length)
    val os = ex.getResponseBody
    os.write(bytes)
    os.close()
  }

  private val page =
    """<!doctype html>
      |<html>
      |<body>
      |<h2>SIMP → JVM bytecode</h2>
      |<form method="POST" action="/compile">
      |<textarea name="src" rows="18" cols="80">a = input; return a;</textarea><br/>
      |<button type="submit">Compile</button>
      |</form>
      |</body>
      |</html>
      |""".stripMargin

  def main(args: Array[String]): Unit = {
    val server = HttpServer.create(new InetSocketAddress("0.0.0.0", 8080), 0)

    server.createContext("/", new HttpHandler {
      def handle(ex: HttpExchange): Unit = {
        respond(ex, 200, "text/html; charset=utf-8", page.getBytes(StandardCharsets.UTF_8))
      }
    })

    server.createContext("/compile", new HttpHandler {
      def handle(ex: HttpExchange): Unit = {
        if (ex.getRequestMethod != "POST") {
          respond(ex, 405, "text/plain; charset=utf-8", "POST only".getBytes(StandardCharsets.UTF_8))
          return
        }

        val body = new String(ex.getRequestBody.readAllBytes(), StandardCharsets.UTF_8)
        // very tiny form decode: expects "src=...."
        val src = java.net.URLDecoder.decode(body.stripPrefix("src="), "UTF-8")

        val tmp = Files.createTempFile("simp-", ".simp")
        Files.writeString(tmp, src, StandardCharsets.UTF_8)

        Main.compile(tmp.toString) match {
          case Left(err) =>
            respond(ex, 400, "text/plain; charset=utf-8", err.getBytes(StandardCharsets.UTF_8))
          case Right(_) =>
            val bytes = Files.readAllBytes(Paths.get("GeneratedClass.class"))
            ex.getResponseHeaders.add("Content-Disposition", "attachment; filename=GeneratedClass.class")
            respond(ex, 200, "application/octet-stream", bytes)
        }
      }
    })

    server.start()
    println("Open http://localhost:8080")
    println("Press ENTER to stop...")
    scala.io.StdIn.readLine()
    server.stop(0)

    println("Open http://localhost:8080")
  }
}
